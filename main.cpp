#include <iostream>
#include <cmath>
#include <cstdint>
#include <random>

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

int JacobiSymbol(uint64_t a, uint64_t n) {
    if (a == 0) return 0;
    int ans = 1;
    if (a < 0) {
        a = -a;
        if (n % 4 == 3) ans = -ans;
    }
    if (a == 1) return 1;
    while (a) {
        if (a < 0) {
            a = -a;
            if (n % 4 == 3) ans = -ans;
        }
        while (a % 2 == 0) {
            a /= 2;
            if (n % 8 == 3 || n % 8 == 5) ans = -ans;
        }
        swap(a, n);
        if (a % 4 == 3 && n % 4 == 3) ans = -ans;
        a %= n;
        if (a > n / 2) a -= n;
    }
    return (n == 1) ? ans : 0;
}

bool Miller_Rabin(uint64_t p) {
    int trials = 20;
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
            y = ModExp(x, 2, p);
            if (y == 1 && x != 1 && x != p - 1) return false;
            x = y;
        }
        if (y != 1) return false;
    }
    return true;
}

uint64_t TrialDivision(uint64_t n) {

    uint64_t N = floor(sqrt(n));
    uint64_t d = 1;

    for (uint64_t i = d + 1; i < N; i++){
        if (n % i == 0) return i;
    }

    return d;
}

uint64_t Polynomial(uint64_t x, uint64_t c, uint64_t n) {
    return ((__uint128_t)x * x + c) % n;
}

uint64_t GCD (uint64_t a, uint64_t b){
    while (b != 0){
        uint64_t temp = b;
        b = a % b;
        a = temp;
    }
    return a;
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


// Pomerance

vector<int64_t> FactorBase(uint64_t n, int B) {
    vector<bool> is_prime(B + 1, true);
    is_prime[0] = -1;
    is_prime[1] = is_prime[2] = false;

    for (int i = 3; (long long)i * i <= B; i++){
        if (is_prime[i]){
            for (int j = i * i; j <= B; j += i) is_prime[j] = false;
        }
    }

    vector<int64_t> fb;
    for (int p = 2; p <= B; p++){
        if (is_prime[p] && ModExp(n % p, (p - 1) / 2, p) == 1) fb.push_back(p);
    }

    return fb;
}

struct Relation {
    uint64_t x;
    vector<int> exponents;
};

vector<Relation> FindRelations(uint64_t n, const vector<uint64_t>& fb, int M) {

    uint64_t m = (uint64_t)sqrtl((long double)n);

    vector<Relation> relations;
    for (int i = 0; i < M; i++) {
        uint64_t a = m + i;
        uint64_t b = (uint64_t)((__uint128_t)a * a - n);

        vector<int> exps(fb.size(), 0);
        for (int j = 0; j < (int)fb.size(); j++)
            while (b % fb[j] == 0) {
                b /= fb[j];
                exps[j]++;
            }

        if (b == 1) relations.push_back({a, move(exps)});
    }
    return relations;
}










void Factorize(uint64_t n, vector<uint64_t>& factors) {
    if (n == 1) return;
    if (Miller_Rabin(n)) { factors.push_back(n); return; }
    uint64_t d = TrialDivision(n);
    if (d == n) {
        for (uint64_t c = 1; d == n || d == 1; c++)
            d = Pollard_rho_Floyd(n, c);
    }
    Factorize(d, factors);
    Factorize(n / d, factors);
}



int main()
{
    uint64_t n = 1184056490329830239;

    if (Miller_Rabin(n)) cout << "Prime";
    else cout << "Composite\n";

    cout << TrialDivision(n) << "\n";
    cout << Pollard_rho_Floyd(n, 2) << "\n";


    return 0;
}




