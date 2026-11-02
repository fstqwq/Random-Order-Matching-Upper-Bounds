// Exact value of the fixed-graph online matching problem (see README.md).
//
// Usage:  solver THREADS < graph.in
// Input:  n m, followed by m undirected edges (vertices numbered 0..n-1),
//         a simple graph with 1 <= n <= 16 and 1 <= m.
// Output: the exact ratio V*(G)/OPT(G) as a reduced fraction on the line
//         "ratio p/q".
//
// Division-free Bellman recurrence. For an observed graph H with r remaining
// edges, unmatched vertices U and C(H) compatible labelings, the
// stored integer is F(H,U) = r! * C(H) * V(H,U). For a child H' with
// Z = (r-1)! * C(H'), each transition contributes
//     multiplicity * max(F(reject), Z + F(accept))
// or multiplicity * F(reject) when acceptance is illegal. This corresponds to
// IntegerSolver.solve in ../lean (see README.md, Correspondence with Lean).
#include <nauty.h>
#include <bits/stdc++.h>
#include <boost/multiprecision/cpp_int.hpp>
#include "vendor-phmap/parallel_hashmap/phmap.h"
using namespace std;
using boost::multiprecision::cpp_int;
using boost::multiprecision::cpp_rational;

using Mask = uint16_t;
using ULL = uint64_t;
const int N = 16;
static_assert(WORDSIZE >= N, "nauty requires a single word per row");
static_assert(HAVE_TLS == 1, "Build and link nauty with thread-local storage");
int n, m;
// Signal handlers may use lock-free atomic operations; workers read atomically.
static_assert(atomic<sig_atomic_t>::is_always_lock_free,
              "Signal handling requires a lock-free atomic stop flag");
atomic<sig_atomic_t> interrupted{0};
atomic<bool> cancelled{false};
void stop_handler(int) { interrupted.store(1, memory_order_relaxed); }
void check_stop() { if (interrupted.load(memory_order_relaxed) || cancelled.load()) throw runtime_error("interrupted"); }
thread_local ULL search_seed=0;
array<Mask, N> host{};
cpp_int factorial[N + 1];
vector<cpp_int> edge_factorial;

struct Graph {
    int k = 0;
    array<Mask, N> adj{};
};

// Return a canonical graph and the old-to-new vertex permutation.
pair<Graph, ULL> canonical(Graph g) {
    if (g.k == 0) {
        return {g, 0};
    }
    graph input[N] = {}, output[N] = {};
    int lab[N], partition[N], orbits[N];
    for (int i = 0; i < g.k; i++) {
        for (int j = 0; j < g.k; j++) {
            if ((g.adj[i] >> j) & 1) {
                ADDELEMENT(input + i, j);
            }
        }
    }
    DEFAULTOPTIONS_GRAPH(options);
    options.getcanon = TRUE;
    statsblk stats;
    densenauty(input, lab, partition, orbits, &options, &stats, 1, g.k, output);
    if (stats.errstatus) {
        throw runtime_error("nauty failed");
    }
    // Validate before lab is used as a shift count.
    unsigned labels_seen = 0;
    for (int i = 0; i < g.k; ++i) {
        if (lab[i] < 0 || lab[i] >= g.k || (labels_seen & (1u << lab[i])))
            throw logic_error("invalid nauty labeling");
        labels_seen |= 1u << lab[i];
    }
    Graph result;
    result.k = g.k;
    ULL permutation = 0;
    for (int i = 0; i < g.k; i++) {
        permutation |= ULL(i) << (4 * lab[i]);
        for (int j = 0; j < g.k; j++) {
            if (ISELEMENT(output + i, j)) {
                result.adj[i] |= 1u << j;
            }
        }
    }
    unsigned used = 0;
    for (int i=0;i<g.k;++i) {
        unsigned v=(permutation>>(4*i))&15;
        if(v>=unsigned(g.k) || (used&(1u<<v))) throw logic_error("invalid permutation");
        used|=1u<<v;
        for(int j=0;j<g.k;++j)
            if (((g.adj[i]>>j)&1) != ((result.adj[v]>>((permutation>>(4*j))&15))&1))
                throw logic_error("invalid graph relabeling");
    }
    return {result, permutation};
}

Mask rename_mask(Mask mask, ULL permutation) {
    Mask result = 0;
    while (mask) {
        int v = __builtin_ctz(mask);
        mask &= mask - 1;
        result |= 1u << ((permutation >> (4 * v)) & 15);
    }
    return result;
}

// Count hidden labelings consistent with the observed edges.
cpp_int count_fits(const Graph &g) {
    array<int, N> order{}, mapping{};
    Mask placed = 0;
    for (int i = 0; i < g.k; i++) {
        int best = -1;
        pair<int, int> score = {-1, -1};
        for (int v = 0; v < g.k; v++) {
            pair<int, int> next = {__builtin_popcount(g.adj[v] & placed),
                                   __builtin_popcount(g.adj[v])};
            if (!(placed >> v & 1) && next > score) {
                best = v;
                score = next;
            }
        }
        order[i] = best;
        placed |= 1u << best;
    }
    auto dfs = [&](auto &&self, int at, Mask used) -> cpp_int {
        check_stop();
        if (at == g.k) {
            return factorial[n - g.k];
        }
        int v = order[at];
        Mask choices = ((1u << n) - 1) & ~used;
        for (int i = 0; i < at; i++) {
            if ((g.adj[v] >> order[i]) & 1) {
                choices &= host[mapping[order[i]]];
            }
        }
        cpp_int result = 0;
        while (choices) {
            int w = __builtin_ctz(choices);
            choices &= choices - 1;
            if (__builtin_popcount(host[w]) >= __builtin_popcount(g.adj[v])) {
                mapping[v] = w;
                result += self(self, at + 1, used | (1u << w));
            }
        }
        return result;
    };
    return dfs(dfs, 0, 0);
}

struct Node;
struct Transition {
    int child;
    Node* target;
    Mask ends, added;
    ULL permutation;
    int multiplicity;
};
struct Node {
    int id=-1;
    ULL graph_hash=0;
    Graph g;
    cpp_int fits;
    int edges;
    once_flag built;
    vector<Transition> next;
    Node(Graph x, cpp_int f, int e):g(x),fits(std::move(f)),edges(e){}
};
mutex registry_mutex;
vector<shared_ptr<Node>> nodes;
struct RegistryShard { mutex lock; unordered_map<string,int> ids; };
array<RegistryShard,64> registry;
struct AnswerHash { size_t operator()(ULL x)const {
    x^=x>>30; x*=0xbf58476d1ce4e5b9ull;
    x^=x>>27; x*=0x94d049bb133111ebull; return x^(x>>31);
} };
using AnswerMap=phmap::parallel_flat_hash_map<ULL,cpp_int,AnswerHash,
    equal_to<ULL>,allocator<pair<const ULL,cpp_int>>,6,shared_mutex>;
AnswerMap memo;
struct ReadEntry { ULL key=ULL(-1); cpp_int value; };
thread_local array<ReadEntry,1024> read_cache;
void remember(ULL key,const cpp_int& value) {
    auto &e=read_cache[AnswerHash{}(key)%read_cache.size()];
    e.key=ULL(-1);
    e.value=value; e.key=key;
}
shared_ptr<Node> node(int id) {
    lock_guard<mutex> guard(registry_mutex);
    return nodes.at(id);
}
bool lookup(ULL key, cpp_int &out) {
    auto &entry=read_cache[AnswerHash{}(key)%read_cache.size()];
    if(entry.key==key) {
        out=entry.value; return true;
    }
    bool found=memo.if_contains(key,[&](const auto &kv){out=kv.second;});
    if(found) remember(key,out);
    return found;
}
cpp_int publish(ULL key,const cpp_int &value) {
    memo.lazy_emplace_l(key,[&](auto &kv){
        if(kv.second!=value) throw logic_error("conflicting complete answers");
    },[&](const auto &ctor){ctor(key,value);});
    remember(key,value);
    return value;
}

int register_graph(const Graph &g) {
    string key(1, char(g.k));
    int edges = 0;
    for (int i = 0; i < g.k; i++) {
        key += char(g.adj[i] & 255);
        key += char(g.adj[i] >> 8);
        edges += __builtin_popcount(g.adj[i]);
    }
    auto &sh=registry[hash<string>{}(key)%registry.size()];
    { lock_guard<mutex> guard(sh.lock);
      auto found=sh.ids.find(key); if(found!=sh.ids.end()) return found->second; }
    auto candidate=make_shared<Node>(g,count_fits(g),edges/2);
    candidate->graph_hash=hash<string>{}(key);
    lock_guard<mutex> shard_guard(sh.lock);
    auto found=sh.ids.find(key); if(found!=sh.ids.end()) return found->second;
    lock_guard<mutex> guard(registry_mutex);
    if (nodes.size() >= size_t(INT_MAX)) throw overflow_error("graph IDs exhausted");
    int id = int(nodes.size());
    candidate->id=id;
    sh.ids[key] = id;
    nodes.push_back(candidate);
    return id;
}

vector<Transition> enumerate_transitions(int id) {
    auto parent=node(id);
    vector<Transition> result;
    if (parent->fits <= 0 || parent->edges >= m) throw logic_error("invalid parent transition state");
    Graph g = parent->g;
    int unseen = n - g.k;
    auto add = [&](int u, int v, int added, int multiplicity) {
        Graph next = g;
        next.k += added;
        next.adj[u] |= 1u << v;
        next.adj[v] |= 1u << u;
        auto [normalized, permutation] = canonical(next);
        int child = register_graph(normalized);
        if (node(child)->fits > 0) {
            Mask fresh = ((1u << next.k) - 1) ^ ((1u << g.k) - 1);
            result.push_back({child, node(child).get(), Mask((1u << u) | (1u << v)),
                                     fresh, permutation, multiplicity});
        }
    };
    for (int u = 0; u < g.k; u++) {
        for (int v = u + 1; v < g.k; v++) {
            if (!(g.adj[u] >> v & 1)) {
                add(u, v, 0, 1);
            }
        }
        if (unseen > 0) {
            add(u, g.k, 1, unseen);
        }
    }
    if (unseen >= 2) {
        add(g.k, g.k + 1, 2, unseen * (unseen - 1) / 2);
    }
    return result;
}
void build_transitions(Node* p) {
    call_once(p->built,[&] { p->next=enumerate_transitions(p->id); });
}

cpp_int solve(Node* p, Mask available) {
    check_stop();
    int id=p->id;
    int remaining = m - p->edges;
    int upper = min(remaining, (__builtin_popcount(available) + n - p->g.k) / 2);
    if (upper == 0) {
        return 0;
    }
    ULL key = (ULL(id) << N) | available;
    cpp_int saved;
    if(lookup(key,saved)) return saved;
    build_transitions(p);
    cpp_int result = 0;
    // Task-dependent rotation avoids herding on the same call_once metadata.
    size_t count=p->next.size();
    ULL order=AnswerHash{}(search_seed^p->graph_hash);
    size_t offset=count?order%count:0;
    for (size_t step=0;step<count;++step) {
        const auto &edge=p->next[(offset+step)%count];
        Mask free = available | edge.added;
        cpp_int best;
        cpp_int scale = edge_factorial[remaining - 1] * edge.target->fits;
        if ((free & edge.ends) == edge.ends) {
            cpp_int accept;
            if(order&1) {
                accept=scale+solve(edge.target,rename_mask(free&~edge.ends,edge.permutation));
                best=solve(edge.target,rename_mask(free,edge.permutation));
            } else {
                best=solve(edge.target,rename_mask(free,edge.permutation));
                accept=scale+solve(edge.target,rename_mask(free&~edge.ends,edge.permutation));
            }
            if(accept>best) best=accept;
        } else best=solve(edge.target,rename_mask(free,edge.permutation));
        result += edge.multiplicity * best;
    }
    return publish(key,result);
}

using State=pair<int,Mask>;
vector<State> frontier(int root,size_t target) {
    vector<State> work{{root,0}};
    for(int depth=0;depth<m && work.size()<target;++depth) {
        std::set<State> next;
        for(auto [id,a]:work) {
            auto p=node(id);
            if(p->edges==m || (__builtin_popcount(a)+n-p->g.k)/2==0) continue;
            build_transitions(p.get());
            for(const auto &e:p->next) {
                Mask free=a|e.added;
                next.emplace(e.child,rename_mask(free,e.permutation));
                if((free&e.ends)==e.ends)
                    next.emplace(e.child,rename_mask(free&~e.ends,e.permutation));
            }
        }
        if(next.empty()) break;
        work.assign(next.begin(),next.end());
    }
    return work;
}
cpp_int parallel_solve(int root,unsigned threads) {
    auto tasks=frontier(root,2*threads);
    atomic<size_t> cursor{0};
    exception_ptr error; mutex error_mutex;
    vector<thread> workers;
    auto body=[&] {
        try {
            while(!cancelled.load()) {
                size_t i=cursor.fetch_add(1); if(i>=tasks.size()) break;
                auto p=node(tasks[i].first);
                search_seed=AnswerHash{}(p->graph_hash^ULL(tasks[i].second));
                solve(p.get(),tasks[i].second);
            }
        } catch(...) {
            cancelled=true;
            lock_guard<mutex> guard(error_mutex);
            if(!error) error=current_exception();
        }
    };
    try { for(unsigned i=0;i<threads;++i) workers.emplace_back(body); }
    catch(...) { cancelled=true; for(auto &t:workers)t.join(); throw; }
    for(auto &t:workers)t.join();
    if(error) rethrow_exception(error);
    return solve(node(root).get(),0);
}

int maximum_matching(Mask mask, vector<int> &dp) {
    if (mask == 0) {
        return 0;
    }
    int &result = dp[mask];
    if (result != -1) {
        return result;
    }
    int v = __builtin_ctz(mask);
    Mask rest = mask & ~(1u << v);
    result = maximum_matching(rest, dp);
    for (Mask choices = host[v] & rest; choices; choices &= choices - 1) {
        int w = __builtin_ctz(choices);
        result = max(result, 1 + maximum_matching(rest & ~(1u << w), dp));
    }
    return result;
}

int main(int argc,char **argv) {
  try {
    unsigned threads=argc>1?stoul(argv[1]):1;
    if(threads<1) throw invalid_argument("threads must be at least 1");
    signal(SIGUSR1,stop_handler); signal(SIGTERM,stop_handler); signal(SIGINT,stop_handler);
    nauty_check(WORDSIZE, 1, N, NAUTYVERSIONID);
    cin >> n >> m;
    if (n < 1 || n > N || m < 1) throw invalid_argument("require 1 <= n <= 16 and m >= 1");
    for (int i = 0; i < m; i++) {
        int u, v;
        cin >> u >> v;
        host[u] |= 1u << v;
        host[v] |= 1u << u;
    }
    factorial[0] = 1;
    for (int i = 1; i <= n; i++) {
        factorial[i] = factorial[i - 1] * i;
    }
    edge_factorial.resize(m + 1);
    edge_factorial[0] = 1;
    for (int i = 1; i <= m; ++i) edge_factorial[i] = edge_factorial[i - 1] * i;
    vector<int> dp(1u << n, -1);
    int optimum = maximum_matching((1u << n) - 1, dp);
    int root=register_graph(Graph{});
    cpp_int answer=parallel_solve(root,threads);
    cout<<"ratio "<<(cpp_rational(answer)/(edge_factorial[m]*factorial[n]*optimum))<<endl;
    return 0;
  } catch(const exception &e) { cerr<<e.what()<<endl; return 2; }
}
