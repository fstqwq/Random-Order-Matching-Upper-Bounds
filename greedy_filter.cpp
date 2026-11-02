// g++ -O3 -std=c++17 greedy_filter.cpp -o greedy_filter
// Read graph6 lines; print "graph6 ratio" when ratio <= threshold + 1e-6.
#include <bits/stdc++.h>

using namespace std;

struct Greedy {
    vector<int> edges, matching;
    vector<double> dp;

    double solve(int mask) {
        if (dp[mask] >= 0) return dp[mask];
        double sum = 0;
        int count = 0, best = 0;
        for (int e : edges) {
            if ((mask & e) != e) continue;
            sum += solve(mask ^ e);
            best = max(best, 1 + matching[mask ^ e]);
            ++count;
        }
        matching[mask] = best;
        return dp[mask] = count ? 1 + sum / count : 0;
    }

    double ratio(const string& line) {
        int n = line[0] - 63, bit = 0;
        edges.clear();
        for (int v = 1; v < n; ++v)
            for (int u = 0; u < v; ++u, ++bit)
                if (((line[1 + bit / 6] - 63) >> (5 - bit % 6)) & 1)
                    edges.push_back((1 << u) | (1 << v));
        dp.assign(1 << n, -1);
        matching.resize(1 << n);
        int full = (1 << n) - 1;
        double value = solve(full);
        return value / matching[full];
    }
};

int main(int argc, char** argv) {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    cout << setprecision(17);
    double threshold = stod(argv[1]);
    Greedy greedy;
    string line;
    while (cin >> line) {
        double value = greedy.ratio(line);
        if (value <= threshold + 1e-6)
            cout << line << ' ' << value << endl;
    }
}
