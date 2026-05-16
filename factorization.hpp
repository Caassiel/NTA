#ifndef FACTORIZATION_HPP
#define FACTORIZATION_HPP

#include <gmpxx.h>
#include <vector>

mpz_class TrialDivision47(const mpz_class& n);
mpz_class Pollard_rho_Floyd(const mpz_class& n, const mpz_class& c);
bool Miller_Rabin(const mpz_class& p, int trials = 20);
std::vector<std::pair<mpz_class,int>> factorize(const mpz_class& n);

bool FactorOverBase(
    mpz_class n,
    const std::vector<mpz_class>& factor_base,
    std::vector<int>& exponents
);

#endif
