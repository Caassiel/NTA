#include <iostream>
#include <cstdint>
#include <vector>
#include <cmath>
using namespace std;

class Group{

public:
    uint64_t p;
    uint64_t a;

    uint64_t ModExp64(uint64_t b, uint64_t e, uint64_t mod) {
        uint64_t x = 1, y = b % mod;
        while (e > 0) {
            if (e & 1) x = (__uint128_t)x * y % mod;
            y = (__uint128_t)y * y % mod;
            e >>= 1;
        }
        return x;
    }

    bool IsGenerator(uint64_t g) {
        uint64_t phi = p - 1;
        uint64_t temp = phi;

        for (uint64_t q = 2; q * q <= temp; q++) {
            if (temp % q == 0) {
                if (ModExp64(g, phi / q, p) == 1)
                    return false;
                while (temp % q == 0)
                    temp /= q;
            }
        }
    }
    const uint64_t n = p - 1;
    uint64_t B = exp(3.38 * sqrt(log(n) * log(log(n))));

    vector<uint64_t> FactorBase(const uint64_t& n, int B) {
        vector<bool> is_prime(B + 1, true);
        is_prime[0] = is_prime[1] = false;
        for (int i = 2; (long long)i * i <= B; i++)
            if (is_prime[i])
                for (int j = i * i; j <= B; j += i) is_prime[j] = false;

        vector<uint64_t> fb;
        for (int p = 2; p <= B; p++) {
            if (!is_prime[p]) continue;
            if (ModExp64(n % p, ((p - 1) / 2), p) == 1)
                fb.push_back(p);
        }
        return fb;
    }

};




int main()
{

    return 0;
}
