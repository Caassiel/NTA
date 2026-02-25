#include <iostream>
#include <cstdint>
using namespace std;


uint64_t ModExp(uint64_t b, uint64_t e, uint64_t mod) {
    uint64_t x = 1, y = b;

    while (e > 0) {
        if (e % 2 == 1) {
            x = (x * y) % mod;
        }
        y = (y * y) % mod;
        e /= 2;
    }
    return x % mod;
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

bool SolovayStrassen(uint64_t p) {
    if (p < 2 || (p % 2 == 0 && p != 2)) return false;
        uint64_t x = rand() % (p - 1) + 1;
        uint64_t jacobi = (p + JacobiSymbol(x, p)) % p;
        uint64_t mod = ModExp(x, (p - 1) / 2, p);
    if (!jacobi || mod != jacobi) return false;
    return true;
}



int main()
{
    uint64_t n = 2147483647;
    if (SolovayStrassen(n)) cout << "yippee";
    else cout << "womp womp";

    return 0;
}
