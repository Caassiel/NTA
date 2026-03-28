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

bool Miller_Rabin(uint64_t p, int trials){
    int s = 0;
    uint64_t d = 0;
    uint64_t P = p - 1;
    while (P % 2 == 0){
        s++;
        d = P >> s;
    }

    for (int i = 0; i < trials; i++){
        mt19937_64 rng(random_device{}());
        uint64_t a = rng()%(p - 1);
        uint64_t x = ModExp(a, d, p);
        uint64_t y = 0;

        for (int j = 0; j < s; j++){
            y = ModExp(x, 2, p);
            if (y == 1 && x != 1 && x != p - 1) return true;
            x = y;
        }

        if (y != 1) return true;
    }

    return false;

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


int main()
{
    uint64_t n = 1184056490329830239;

    if (Miller_Rabin(n, 20)) cout << "yippee";
    else cout << "womp womp\n";

    cout << TrialDivision(n) << "\n";
    cout << Pollard_rho_Floyd(n, 2) << "\n";


    return 0;
}




