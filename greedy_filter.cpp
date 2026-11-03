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
        /*
        GPT 6 Astra comment: For n <= 16, IEEE binary64 round-to-nearest
        arithmetic (no fast-math) makes 1e-6 conservative. Each nonnegative
        DP step sums at most 120 terms, divides, and adds 1; a dependency
        path has at most 8 steps. Including division by the exact integer
        OPT, the relative error is at most gamma_977 = 977*u/(1-977*u),
        u = 2^-53. The true Greedy ratio is <= 1, so this also bounds its
        absolute error (< 1.1e-13). For thresholds in [0,1], threshold
        conversion and rounding of threshold + 1e-6 keep the total error
        below 1e-12; 17-digit output round-trips the computed double.
        Thus neither this test nor the same test in enumerate_graphs.py
        can discard a graph whose true optimal ratio is below threshold,
        since its true Greedy ratio is no larger than its optimal ratio.
        */
        if (value <= threshold + 1e-6)
            cout << line << ' ' << value << endl;
    }
}
