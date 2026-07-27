#include <cstdint>
#include <iostream>
#include <vector>

using i64 = long long;

static std::vector<int> primes_up_to(int N) {
    std::vector<bool> a(N + 1, true);
    a[0] = a[1] = false;
    for (int i = 2; 1LL * i * i <= N; ++i)
        if (a[i]) for (int j = i * i; j <= N; j += i) a[j] = false;
    std::vector<int> ps;
    for (int i = 2; i <= N; ++i) if (a[i]) ps.push_back(i);
    return ps;
}

static inline int norm(i64 x, int p) {
    x %= p;
    if (x < 0) x += p;
    return static_cast<int>(x);
}

int main() {
    constexpr int LIMIT = 100000;
    int max_mult = 0;
    long long double_count = 0, noncentral_double_count = 0, triple_count = 0;

    for (int p : primes_up_to(LIMIT)) {
        if (p < 5) continue;
        std::vector<int> inv(p);
        inv[1] = 1;
        for (int i = 2; i < p; ++i)
            inv[i] = norm(p - 1LL * (p / i) * inv[p % i], p);

        // U_0, U_1 and their first two parameter derivatives at s=0.
        int bm1 = 1, b = 5 % p;
        int cm1 = 0, c = 12 % p;
        int em1 = 0, e = 0;

        auto inspect = [&](int m, int bv, int cv, int ev) {
            int mult = (bv != 0 ? 0 : (cv != 0 ? 1 : (ev != 0 ? 2 : 3)));
            if (mult > max_mult) {
                max_mult = mult;
                std::cout << "NEW_MAX p=" << p << " j=" << (m + 1)
                          << " m=" << m << " mult_at_least=" << mult
                          << " b,c,e=" << bv << ',' << cv << ',' << ev << '\n';
            }
            if (mult >= 2) {
                ++double_count;
                const bool central = (2 * m + 1 == p);
                if (!central) {
                    ++noncentral_double_count;
                    if (noncentral_double_count <= 30)
                        std::cout << "NONCENTRAL_DOUBLE p=" << p << " j=" << (m + 1)
                                  << " m=" << m << " b,c,e=" << bv << ',' << cv << ',' << ev << '\n';
                }
            }
            if (mult >= 3) {
                ++triple_count;
                std::cout << "TRIPLE p=" << p << " j=" << (m + 1)
                          << " m=" << m << " b,c,e=" << bv << ',' << cv << ',' << ev << '\n';
            }
        };

        inspect(1, b, c, e);
        for (int n = 1; n <= p - 3; ++n) {
            const i64 n2 = 1LL * n * n % p;
            const i64 n3 = n2 * n % p;
            const int np1 = n + 1;
            const i64 u2 = 1LL * np1 * np1 % p;
            const i64 u3 = u2 * np1 % p;
            const i64 inv3 = 1LL * inv[np1] * inv[np1] % p * inv[np1] % p;

            const int An = norm(34 * n3 + 51 * n2 + 27LL * n + 5, p);
            const int A1 = norm(102 * n2 + 102LL * n + 27, p);
            const int A2 = norm(204LL * n + 102, p);

            const int bn = norm((1LL * An * b - n3 * bm1) * inv3, p);
            const int cn = norm((1LL * An * c - n3 * cm1 + 1LL * A1 * b
                               - 3LL * u2 * bn - 3LL * n2 * bm1) * inv3, p);
            const int en = norm((1LL * An * e - n3 * em1 + 2LL * A1 * c + 1LL * A2 * b
                               - 6LL * u2 * cn - 6LL * np1 * bn
                               - 6LL * n2 * cm1 - 6LL * n * bm1) * inv3, p);

            bm1 = b; b = bn;
            cm1 = c; c = cn;
            em1 = e; e = en;
            inspect(n + 1, b, c, e);
            if (triple_count >= 30) break;
        }
        if (triple_count >= 30) break;
    }

    std::cout << "SUMMARY limit=" << LIMIT
              << " max_mult_at_least=" << max_mult
              << " doubles=" << double_count
              << " noncentral_doubles=" << noncentral_double_count
              << " triples=" << triple_count << '\n';
}
