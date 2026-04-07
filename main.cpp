#include <iostream>
#include <cmath>
#include <vector>
#include <cassert>
#include <bitset>
#include <chrono>
#include <iomanip>
#include <string>
#include <random>
#include <gmpxx.h>

using namespace std;
using namespace chrono;

gmp_randclass& rng() {
    static gmp_randclass r(gmp_randinit_mt);
    static bool seeded = false;
    if (!seeded) { r.seed(random_device{}()); seeded = true; }
    return r;
}

mpz_class ModExp(const mpz_class& b, const mpz_class& e, const mpz_class& mod) {
    mpz_class result;
    mpz_powm(result.get_mpz_t(), b.get_mpz_t(), e.get_mpz_t(), mod.get_mpz_t());
    return result;
}

mpz_class GCD(const mpz_class& a, const mpz_class& b) {
    mpz_class result;
    mpz_gcd(result.get_mpz_t(), a.get_mpz_t(), b.get_mpz_t());
    return result;
}

uint64_t ModExp64(uint64_t b, uint64_t e, uint64_t mod) {
    uint64_t x = 1, y = b % mod;
    while (e > 0) {
        if (e & 1) x = (__uint128_t)x * y % mod;
        y = (__uint128_t)y * y % mod;
        e >>= 1;
    }
    return x;
}

bool Miller_Rabin(const mpz_class& p, int trials = 20) {
    if (p < 2) return false;
    if (p == 2 || p == 3) return true;
    if (p % 2 == 0) return false;

    int s = 0;
    mpz_class d = p - 1;
    while (d % 2 == 0) { d >>= 1; s++; }

    for (int i = 0; i < trials; i++) {
        mpz_class a = rng().get_z_range(p - 4) + 2;
        mpz_class x = ModExp(a, d, p);
        mpz_class y = 0;
        for (int j = 0; j < s; j++) {
            y = x * x % p;
            if (y == 1 && x != 1 && x != p - 1) return false;
            x = y;
        }
        if (y != 1) return false;
    }
    return true;
}

//Trial division
mpz_class TrialDivision47(const mpz_class& n) {
    static const long small_primes[] = {
        2,3,5,7,11,13,17,19,23,29,31,37,41,43,47
    };
    for (long p : small_primes)
        if (n % p == 0) return mpz_class(p);
    return n;
}

//Pollard rho
mpz_class Polynomial(const mpz_class& x, const mpz_class& c, const mpz_class& n) {
    return (x * x + c) % n;
}

mpz_class Pollard_rho_Floyd(const mpz_class& n, const mpz_class& c) {
    if (n % 2 == 0) return mpz_class(2);
    mpz_class x = rng().get_z_range(n - 4) + 2;
    mpz_class y = x, d = 1;
    while (d == 1) {
        x = Polynomial(x, c, n);
        y = Polynomial(Polynomial(y, c, n), c, n);
        mpz_class diff = x > y ? x - y : y - x;
        d = GCD(diff, n);
    }
    return (d == n) ? mpz_class(1) : d;
}

//Pomerance
int64_t TonelliShanks(uint64_t n, uint64_t p) {
    n %= p;
    if (n == 0) return 0;
    if (p == 2) return n & 1;
    if (ModExp64(n, (p - 1) / 2, p) != 1) return -1;
    if (p % 4 == 3) return (int64_t)ModExp64(n, (p + 1) / 4, p);

    uint64_t S = 0, Q = p - 1;
    while (Q % 2 == 0) { Q >>= 1; S++; }

    uint64_t z = 2;
    while (ModExp64(z, (p - 1) / 2, p) != p - 1) z++;

    uint64_t M = S;
    uint64_t c = ModExp64(z, Q, p);
    uint64_t t = ModExp64(n, Q, p);
    uint64_t R = ModExp64(n, (Q + 1) / 2, p);

    for (;;) {
        if (t == 1) return (int64_t)R;
        uint64_t i = 1;
        uint64_t tmp = (__uint128_t)t * t % p;
        while (tmp != 1) { tmp = (__uint128_t)tmp * tmp % p; i++; }
        uint64_t b = c;
        for (uint64_t j = 0; j < M - i - 1; j++) b = (__uint128_t)b * b % p;
        M = i;
        c = (__uint128_t)b * b % p;
        t = (__uint128_t)t * c % p;
        R = (__uint128_t)R * b % p;
    }
}

vector<uint64_t> FactorBase(const mpz_class& n, int B) {
    vector<bool> is_prime(B + 1, true);
    is_prime[0] = is_prime[1] = false;
    for (int i = 2; (long long)i * i <= B; i++)
        if (is_prime[i])
            for (int j = i * i; j <= B; j += i) is_prime[j] = false;

    vector<uint64_t> fb;
    for (int p = 2; p <= B; p++) {
        if (!is_prime[p]) continue;
        uint64_t np = (uint64_t)mpz_fdiv_ui(n.get_mpz_t(), (unsigned long)p);
        if (ModExp64(np, (uint64_t)(p - 1) / 2, (uint64_t)p) == 1)
            fb.push_back((uint64_t)p);
    }
    return fb;
}

struct Relation {
    mpz_class x;
    vector<int> exponents;
};

vector<Relation> Sieve(const mpz_class& n, const vector<uint64_t>& fb, int M) {
    mpz_class sqrtn;
    mpz_sqrt(sqrtn.get_mpz_t(), n.get_mpz_t());
    while ((sqrtn + 1) * (sqrtn + 1) <= n) sqrtn++;
    while (sqrtn * sqrtn > n) sqrtn--;
    sqrtn++;

    int sz = 2 * M;
    vector<float> logs(sz, 0.0f);

    for (uint64_t p : fb) {
        uint64_t np      = (uint64_t)mpz_fdiv_ui(n.get_mpz_t(),     (unsigned long)p);
        uint64_t sqrtn_p = (uint64_t)mpz_fdiv_ui(sqrtn.get_mpz_t(), (unsigned long)p);
        int64_t  r       = TonelliShanks(np, p);
        if (r < 0) continue;

        float logp = log2f((float)p);
        for (int64_t root : {r, (int64_t)p - r}) {
            int64_t start = ((root - (int64_t)sqrtn_p) % (int64_t)p + (int64_t)p) % (int64_t)p;
            for (int64_t i = start; i < sz; i += (int64_t)p)
                logs[i] += logp;
        }
    }

    float logn_bits = (float)mpz_sizeinbase(n.get_mpz_t(), 2);
    float threshold = logn_bits * 0.5f + log2f((float)M) - 1.5f;

    vector<Relation> relations;
    for (int i = 0; i < sz; i++) {
        if (logs[i] < threshold) continue;

        mpz_class xi  = sqrtn + (unsigned long)i;
        mpz_class rem = xi * xi - n;

        vector<int> exps(fb.size(), 0);
        for (int j = 0; j < (int)fb.size(); j++)
            while (mpz_divisible_ui_p(rem.get_mpz_t(), (unsigned long)fb[j])) {
                mpz_divexact_ui(rem.get_mpz_t(), rem.get_mpz_t(), (unsigned long)fb[j]);
                exps[j]++;
            }

        if (rem == 1) relations.push_back({xi, move(exps)});
    }
    return relations;
}

const int BITSET_SIZE = 65536;

vector<vector<int>> FindAllDependencies(const vector<Relation>& rels, int fb_size) {
    int nr = (int)rels.size();
    assert(fb_size + nr <= BITSET_SIZE);

    vector<bitset<BITSET_SIZE>> mat(nr);
    for (int i = 0; i < nr; i++) {
        for (int j = 0; j < fb_size; j++)
            mat[i][j] = rels[i].exponents[j] & 1;
        mat[i][fb_size + i] = 1;
    }

    int pivot_row = 0;
    for (int col = 0; col < fb_size && pivot_row < nr; col++) {
        int pivot = -1;
        for (int row = pivot_row; row < nr; row++)
            if (mat[row][col]) { pivot = row; break; }
        if (pivot == -1) continue;

        swap(mat[pivot_row], mat[pivot]);
        for (int row = 0; row < nr; row++)
            if (row != pivot_row && mat[row][col])
                mat[row] ^= mat[pivot_row];
        pivot_row++;
    }

    vector<vector<int>> all_deps;
    for (int i = 0; i < nr; i++) {
        bool zero = true;
        for (int j = 0; j < fb_size; j++)
            if (mat[i][j]) { zero = false; break; }
        if (!zero) continue;

        vector<int> idx;
        for (int j = 0; j < nr; j++)
            if (mat[i][fb_size + j]) idx.push_back(j);
        if (!idx.empty()) all_deps.push_back(idx);
    }
    return all_deps;
}

mpz_class ExtractFactor(const mpz_class& n, const vector<Relation>& rels,
                        const vector<int>& idx, const vector<uint64_t>& fb) {
    mpz_class x = 1;
    vector<int> total(fb.size(), 0);
    for (int i : idx) {
        x = x * rels[i].x % n;
        for (int j = 0; j < (int)fb.size(); j++)
            total[j] += rels[i].exponents[j];
    }

    mpz_class y = 1;
    for (int j = 0; j < (int)fb.size(); j++)
        for (int k = 0; k < total[j] / 2; k++)
            y = y * (unsigned long)fb[j] % n;

    mpz_class diff = x > y ? x - y : y - x;
    mpz_class f = GCD(diff, n);
    return (f == 1 || f == n) ? mpz_class(0) : f;
}

mpz_class QuadraticSieve(const mpz_class& n) {
    if (n % 2 == 0) return mpz_class(2);
    for (long p : {3L,5L,7L,11L,13L,17L,19L,23L,29L,31L,37L,41L,43L,47L})
        if (n % p == 0) return mpz_class(p);

    double logn = (double)mpz_sizeinbase(n.get_mpz_t(), 2) * log(2.0);
    int B = max((int)exp(0.56 /*0,7*/ * sqrt(logn * log(logn))), 1000);
    int M = B * 25;

    auto fb     = FactorBase(n, B);
    int  needed = (int)fb.size() + 20;

    vector<Relation> relations;
    for (int attempt = 0; (int)relations.size() < needed && attempt < 15; attempt++) {
        auto batch = Sieve(n, fb, M);
        for (auto& r : batch) {
            //if  ((int)relations.size() >= needed) break;
            relations.push_back(move(r));
        }
        M *= 2;
    }

    if ((int)relations.size() < needed) return mpz_class(0);

    auto all_deps = FindAllDependencies(relations, (int)fb.size());
    for (auto& dep : all_deps) {
        mpz_class f = ExtractFactor(n, relations, dep, fb);
        if (f != 0) return f;
    }
    return mpz_class(0);
}

//program
struct FactorRecord {
    mpz_class factor;
    string    algorithm;
    double    time_ms;
};

vector<FactorRecord> g_factors;

template<typename F>
auto timed_call(F&& f) {
    auto t0     = high_resolution_clock::now();
    auto result = f();
    double ms   = duration<double, milli>(high_resolution_clock::now() - t0).count();
    return make_pair(result, ms);
}

void record(const mpz_class& factor, const string& algo, double ms) {
    g_factors.push_back({factor, algo, ms});
    cout << "  >> Factor found: " << factor
         << "  [" << algo << ", "
         << fixed << setprecision(3) << ms << " ms]\n";
}

void step_a(const mpz_class& n, const string& found_by = "Miller-Rabin");
void step_b(const mpz_class& n);
void step_c(const mpz_class& n);
void step_d(const mpz_class& n, const string& found_by = "Miller-Rabin");
void step_e(const mpz_class& n);

void step_a(const mpz_class& n, const string& found_by) {
    if (n <= 1) return;
    cout << "\n[a] Miller-Rabin test on " << n << "\n";
    auto [is_prime, ms] = timed_call([&]{ return Miller_Rabin(n); });
    if (is_prime) { record(n, found_by, ms); return; }
    cout << "    Composite (" << fixed << setprecision(3) << ms << " ms)\n";
    step_b(n);
}

void step_b(const mpz_class& n) {
    cout << "[b] Trial division (<=47) on " << n << "\n";
    auto [a, ms] = timed_call([&]{ return TrialDivision47(n); });
    if (a != n) {
        record(a, "Trial Division", ms);
        step_a(n / a);
        return;
    }
    cout << "    No factor <= 47 found (" << fixed << setprecision(3) << ms << " ms)\n";
    step_c(n);
}

void step_c(const mpz_class& n) {
    cout << "[c] Pollard-rho on " << n << "\n";
    auto [a, ms] = timed_call([&]{
        for (long c = 1; c <= 2; c++) {
            mpz_class d = Pollard_rho_Floyd(n, mpz_class(c));
            if (d != 1 && d != n) return d;
        }
        return mpz_class(1);
    });
    if (a != 1 && a != n) {
        cout << "    Factor " << a << " found (" << fixed << setprecision(3) << ms << " ms)\n";
        step_a(a, "Pollard-rho");
        step_d(n / a, "Pollard-rho");
        return;
    }
    cout << "    Pollard-rho failed (" << fixed << setprecision(3) << ms << " ms)\n";
    step_e(n);
}

void step_d(const mpz_class& n, const string& found_by) {
    if (n <= 1) return;
    cout << "\n[d] Miller-Rabin test on " << n << "\n";
    auto [is_prime, ms] = timed_call([&]{ return Miller_Rabin(n); });
    if (is_prime) { record(n, found_by, ms); return; }
    cout << "    Composite (" << fixed << setprecision(3) << ms << " ms)\n";
    step_e(n);
}

void step_e(const mpz_class& n) {
    cout << "[e] Quadratic Sieve on " << n << "\n";
    auto [a, ms] = timed_call([&]{ return QuadraticSieve(n); });
    if (a != 0 && a != n) {
        record(a, "Quadratic Sieve", ms);
        step_d(n / a, "Quadratic Sieve");
        return;
    }
    cout << "    ERROR: failed to factor " << n
         << " (" << fixed << setprecision(3) << ms << " ms)\n";
}


int main(int argc, char* argv[]) {
    mpz_class n;

    if (argc >= 2) {
        try {
            n = mpz_class(argv[1]);
        } catch (...) {
            cerr << "Invalid input. \n";
            return 1;
        }
    } else {
        cout << "Enter n: ";
        cin >> n;
    }

    cout << "Factorizing " << n << "\n";
    step_a(n);

    cout << "\n" << string(65, '=') << "\n";
    cout << "Result: " << n << " = ";
    for (int i = 0; i < (int)g_factors.size(); i++) {
        if (i) cout << " * ";
        cout << g_factors[i].factor;
    }
    cout << "\n" << string(65, '=') << "\n\n";

    cout << left
         << setw(30) << "Factor"
         << setw(28) << "Algorithm"
         << "Time (ms)\n";
    cout << string(65, '-') << "\n";

    double total_ms = 0;
    for (auto& r : g_factors) {
        cout << setw(30) << r.factor
             << setw(28) << r.algorithm
             << fixed << setprecision(3) << r.time_ms << "\n";
        total_ms += r.time_ms;
    }

    cout << string(65, '-') << "\n";
    cout << setw(58) << "Total"
         << fixed << setprecision(3) << total_ms << " ms\n";


    vector<mpz_class> array1 = {
        mpz_class("3009182572376191"),
        mpz_class("1021514194991569"),
        mpz_class("4000852962116741"),
        mpz_class("15196946347083"),
        mpz_class("499664789704823"),
        mpz_class("269322119833303"),
        mpz_class("679321846483919"),
        mpz_class("96267366284849"),
        mpz_class("61333127792637"),
        mpz_class("2485021628404193")
    };

    vector<mpz_class> array2 = {
        mpz_class("901667173167834173"),
        mpz_class("323324583518541583"),
        mpz_class("2500744714570633849"),
        mpz_class("691534156424661573"),
        mpz_class("1184056490329830239"),
        mpz_class("1449863225586482579"),
        mpz_class("778320232076288167"),
        mpz_class("1515475730401555091"),
        mpz_class("341012868237902669"),
        mpz_class("7442109405582674149")
    };

    cout << left
         << setw(22) << "n"
         << setw(20) << "Pollard factor"
         << setw(12) << "P-rho ms"
         << setw(20) << "QS factor"
         << "QS ms\n";
    cout << string(78, '-') << "\n";
    for (const mpz_class& m : array1) {
        auto [a, ms1] = timed_call([&]{ return Pollard_rho_Floyd(m, mpz_class(1)); });
        auto [b, ms2] = timed_call([&]{ return QuadraticSieve(m); });
        cout << setw(22) << m
             << setw(20) << a
             << setw(12) << fixed << setprecision(3) << ms1
             << setw(20) << b
             << fixed << setprecision(3) << ms2 << "\n";
    }

    return 0;
}





