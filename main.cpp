#include <iostream>
#include <cmath>
#include <cstdint>
#include <random>
#include <vector>

using namespace std;


uint64_t ModExp(uint64_t b, uint64_t e, uint64_t mod) {
    uint64_t x = 1, y = b % mod;
    while (e > 0) {
        if (e & 1) x = (__uint128_t)x * y % mod;
        y = (__uint128_t)y * y % mod;
        e >>= 1;
    }
    return x;
}

uint64_t GCD(uint64_t a, uint64_t b) {
    while (b != 0) {
        uint64_t temp = b;
        b = a % b;
        a = temp;
    }
    return a;
}


bool Miller_Rabin(uint64_t p, int trials = 20) {
    if (p < 2) return false;
    if (p == 2 || p == 3) return true;
    if (p % 2 == 0) return false;

    int s = 0;
    uint64_t d = p - 1;
    while (d % 2 == 0) {
        d >>= 1;
        s++;
    }

    mt19937_64 rng(random_device{}());
    uniform_int_distribution<uint64_t> dist(2, p - 3);

    for (int i = 0; i < trials; i++) {
        uint64_t a = dist(rng);
        uint64_t x = ModExp(a, d, p);
        uint64_t y = 0;
        for (int j = 0; j < s; j++) {
            y = (__uint128_t)x * x % p;
            if (y == 1 && x != 1 && x != p - 1) return false;
            x = y;
        }
        if (y != 1) return false;
    }
    return true;
}

uint64_t TrialDivision(uint64_t n) {
    if (n % 2 == 0) return 2;
    uint64_t N = (uint64_t)sqrtl((long double)n);
    while (N * N < n) N++;
    for (uint64_t i = 3; i <= N; i += 2)
        if (n % i == 0) return i;
    return n;
}

uint64_t TrialDivision47(uint64_t n) {
    static const uint64_t small_primes[] = {
        2,3,5,7,11,13,17,19,23,29,31,37,41,43,47
    };
    for (uint64_t p : small_primes)
        if (n % p == 0) return p;
    return n;
}


uint64_t Polynomial(uint64_t x, uint64_t c, uint64_t n) {
    return ((__uint128_t)x * x + c) % n;
}

uint64_t Pollard_rho_Floyd(uint64_t n, uint64_t c) {
    if (n % 2 == 0) return 2;
    mt19937_64 rng(random_device{}());
    uint64_t x = rng() % (n - 2) + 2;
    uint64_t y = x;
    uint64_t d = 1;
    while (d == 1) {
        x = Polynomial(x, c, n);
        y = Polynomial(Polynomial(y, c, n), c, n);
        d = GCD(x > y ? x - y : y - x, n);
    }
    return (d == n) ? 1 : d;
}

//Pomerance

vector<uint64_t> FactorBase(uint64_t n, int B) {
    vector<bool> is_prime(B + 1, true);
    is_prime[0] = is_prime[1] = false;
    for (int i = 2; (long long)i * i <= B; i++)
        if (is_prime[i])
            for (int j = i * i; j <= B; j += i) is_prime[j] = false;

    vector<uint64_t> fb;
    for (int p = 2; p <= B; p++)
        if (is_prime[p] && ModExp(n % p, (p - 1) / 2, p) == 1)
            fb.push_back(p);

    return fb;
}

struct Relation {
    uint64_t x;
    vector<int> exponents;
};

vector<Relation> FindRelations(uint64_t n, const vector<uint64_t>& fb, int M) {
    uint64_t m = (uint64_t)sqrtl((long double)n);
    while ((__uint128_t)m * m > n) m--;
    while ((__uint128_t)(m + 1) * (m + 1) <= n) m++;
    m++;

    vector<Relation> relations;
    for (int i = 0; i < M; i++) {
        uint64_t a = m + (uint64_t)i;
        uint64_t b = (uint64_t)((__uint128_t)a * a - n);

        vector<int> exps(fb.size(), 0);
        for (int j = 0; j < (int)fb.size(); j++)
            while (b % fb[j] == 0) { b /= fb[j]; exps[j]++; }

        if (b == 1) relations.push_back({a, move(exps)});
    }
    return relations;
}

const int BITSET_SIZE = 2048;

optional<vector<int>> FindDependency(const vector<Relation>& rels, int fb_size) {

    int nr = (int)rels.size();
    assert(fb_size + nr <= BITSET_SIZE);

    vector<bitset<BITSET_SIZE>> mat(nr);
    for (int i = 0; i < nr; i++) {
        for (int j = 0; j < fb_size; j++) mat[i][j] = rels[i].exponents[j] & 1;
        mat[i][fb_size + i] = 1;
    }

    int pivot_row = 0;

    for (int col = 0; col < fb_size && pivot_row < nr; col++) {
        int pivot = -1;
        for (int row = pivot_row; row < nr; row++)
            if (mat[row][col]) {
                pivot = row;
                break;
            }
        if (pivot == -1) continue;

        swap(mat[pivot_row], mat[pivot]);

        for (int row = 0; row < nr; row++) if (row != pivot_row && mat[row][col]) mat[row] ^= mat[pivot_row];
        pivot_row++;
    }

    for (int i = 0; i < nr; i++) {
        bool zero = true;
        for (int j = 0; j < fb_size; j++)
            if (mat[i][j]) {
                zero = false;
                break;
            }
        if (!zero) continue;

        vector<int> idx;
        for (int j = 0; j < nr; j++) if (mat[i][fb_size + j]) idx.push_back(j);
        if (!idx.empty()) return idx;
    }

    return nullopt;
}

uint64_t ExtractFactor(uint64_t n, const vector<Relation>& rels, const vector<int>& idx, const vector<uint64_t>& fb) {
    uint64_t x = 1;
    vector<int> total(fb.size(), 0);
    for (int i : idx) {
        x = (__uint128_t)x * rels[i].x % n;
        for (int j = 0; j < (int)fb.size(); j++) total[j] += rels[i].exponents[j];
    }

    uint64_t y = 1;
    for (int j = 0; j < (int)fb.size(); j++)
        for (int k = 0; k < total[j] / 2; k++)
            y = (__uint128_t)y * fb[j] % n;

    uint64_t diff = x > y ? x - y : y - x;
    uint64_t f = GCD(diff, n);
    return (f == 1 || f == n) ? 0 : f;
}

uint64_t QuadraticSieve(uint64_t n) {
    if (n % 2 == 0) return 2;

    double logn = log((double)n);
    int B = max((int)exp(0.5 * sqrt(logn * log(logn))), 200); // heuristic
    int M = B * 8;
    auto fb = FactorBase(n, B);
    int needed = (int)fb.size() + 20;
    vector<Relation> relations;

    for (int attempt = 0; (int)relations.size() < needed && attempt < 8; attempt++) {
        auto batch = FindRelations(n, fb, M);
        for (auto& r : batch) relations.push_back(move(r));
        M *= 2;
    }

    if ((int)relations.size() < needed) return 0;
    auto dep = FindDependency(relations, (int)fb.size());
    if (!dep) return 0;

    return ExtractFactor(n, relations, *dep, fb);
}

void Factorize(uint64_t n, vector<uint64_t>& factors) {
    if (n == 1) return;
    if (Miller_Rabin(n)) { factors.push_back(n); return; }

    uint64_t d = TrialDivision(n);
    if (d == n) {
        d = 1;
        for (uint64_t c = 1; d == 1 || d == n; c++)
            d = Pollard_rho_Floyd(n, c);
    }

    Factorize(d, factors);
    Factorize(n / d, factors);
}



int main() {
    uint64_t n = 1184056490329830239;

    if (Miller_Rabin(n)) cout << n << " is prime\n";
    else {
        cout << n << " is composite\n";
        vector<uint64_t> factors;
        Factorize(n, factors);
        cout << "Factors: ";
        for (uint64_t f : factors) cout << f << " ";
        cout << "\n";
    }

    return 0;
}



