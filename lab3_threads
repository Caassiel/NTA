#include <iostream>
#include <cmath>
#include <vector>
#include <bitset>
#include <chrono>
#include <iomanip>
#include <string>
#include <random>
#include <gmpxx.h>
#include <map>

#include <thread>
#include <mutex>
#include <atomic>
using namespace std;

#include "from_lab1.cpp"

mpz_class TrialDivision47(const mpz_class& n);
mpz_class Pollard_rho_Floyd(const mpz_class& n, const mpz_class& c);
bool Miller_Rabin(const mpz_class& p, int trials);
vector<pair<mpz_class,int>> factorize(const mpz_class& n);

bool FactorOverBase(
    mpz_class n,
    const vector<mpz_class>& factor_base,
    vector<int>& exponents
);

mpz_class mod_inverse(mpz_class a, mpz_class m) {
    mpz_class x, y, gcd;
    mpz_gcdext(gcd.get_mpz_t(), x.get_mpz_t(), y.get_mpz_t(), a.get_mpz_t(), m.get_mpz_t());

    x %= m;
    if (x < 0) x += m;
    return x;
}

mpz_class CRT(vector<mpz_class> res, vector<mpz_class> mod) {
    mpz_class M = 1;
    for (auto &x : mod) M *= x;
    mpz_class result = 0;
    for (size_t i = 0; i < mod.size(); i++) {
        mpz_class Mi = M / mod[i];
        mpz_class inv = mod_inverse(Mi % mod[i], mod[i]);
        result += (res[i] * Mi % M) * inv;
    }
    return result % M;
}

class IndexCalculus {
public:
    mpz_class p, a, n;
    vector<mpz_class> factor_base;
    map<mpz_class, vector<int>> relations;
    mutex rel_mtx;
    atomic<int> rel_count{0};

    IndexCalculus(const mpz_class& p, const mpz_class& a): p(p), a(a), n(p-1) {}

    void buildFactorBase(int B) {
        for (int i = 2; i <= B; i++) {
            mpz_class k(i);
            if (Miller_Rabin(k)) factor_base.push_back(i);
        }
    }

    bool isSmooth(mpz_class n, vector<int>& exponents) {
        return FactorOverBase(n, factor_base, exponents);
    }


    static void relation_worker(IndexCalculus* ic, int required, const mpz_class& order, map<mpz_class, vector<int>>& relations, mutex& mtx, atomic<int>& count){
        gmp_randclass rng(gmp_randinit_mt);
        rng.seed(time(nullptr) ^ hash<thread::id>{}(this_thread::get_id()));

        while (count.load() < required) {
            mpz_class k = rng.get_z_range(order - 1) + 1;

            mpz_class val;
            mpz_powm(val.get_mpz_t(),
                      ic->a.get_mpz_t(),
                      k.get_mpz_t(),
                      ic->p.get_mpz_t());

            vector<int> exps;
            if (ic->isSmooth(val, exps)) {
                lock_guard<mutex> lock(mtx);

                if (relations.find(k) == relations.end()) {
                    relations[k] = exps;
                    count++;
                }
            }
        }
    }

   void collectRelations(int required){
        int T = thread::hardware_concurrency();
        if (T == 0) T = 4;

        vector<thread> threads;

        rel_count = 0;

        mpz_class order = p - 1;

        for (int i = 0; i < T; i++) {
            threads.emplace_back(
                relation_worker,
                this,
                required,
                cref(order),
                ref(relations),
                ref(rel_mtx),
                ref(rel_count)
            );
        }

        for (auto& t : threads) t.join();
    }

    mpz_class solve(const mpz_class& b);

    vector<mpz_class> solveLinearSystem();
};


vector<mpz_class> IndexCalculus::solveLinearSystem() {
    mpz_class mod = p - 1;

    int n = factor_base.size();
    int m = relations.size();

    vector<vector<mpz_class>> A(m, vector<mpz_class>(n));
    vector<mpz_class> bvec(m);

    int row = 0;
    for (auto& [k, exps] : relations) {
        bvec[row] = k % mod;
        for (int j = 0; j < n; j++)
            A[row][j] = exps[j] % mod;
        row++;
    }

    auto factors = factorize(mod);

    vector<mpz_class> moduli;
    vector<vector<mpz_class>> solutions_per_mod;

    for (auto& [prime, exp] : factors) {
        mpz_class q;
        mpz_pow_ui(q.get_mpz_t(), prime.get_mpz_t(), (unsigned)exp);
        moduli.push_back(q);

        vector<vector<mpz_class>> Aq = A;
        vector<mpz_class> bq = bvec;

        for (int i = 0; i < m; i++) {
            bq[i] %= q;
            if (bq[i] < 0) bq[i] += q;
            for (int j = 0; j < n; j++) {
                Aq[i][j] %= q;
                if (Aq[i][j] < 0) Aq[i][j] += q;
            }
        }
        int r = 0;
        vector<int> pivot_col(n, -1);

        for (int col = 0; col < n && r < m; col++) {
            int pivot = -1;

            for (int i = r; i < m; i++) {
                mpz_class g;
                mpz_gcd(g.get_mpz_t(), Aq[i][col].get_mpz_t(), q.get_mpz_t());
                if (g == 1) {
                    pivot = i;
                    break;
                }
            }

            if (pivot == -1) continue;

            swap(Aq[r], Aq[pivot]);
            swap(bq[r], bq[pivot]);

            vector<bool> determined(n, false);
            pivot_col[col] = r;
            if (pivot_col[col] != -1) determined[col] = true;

            mpz_class inv;
            mpz_invert(inv.get_mpz_t(), Aq[r][col].get_mpz_t(), q.get_mpz_t());

            for (int j = col; j < n; j++)
                Aq[r][j] = (Aq[r][j] * inv) % q;

            bq[r] = (bq[r] * inv) % q;

            for (int i = 0; i < m; i++) {
                if (i == r) continue;

                if (Aq[i][col] != 0) {
                    mpz_class factor = Aq[i][col];

                    for (int j = col; j < n; j++) {
                        Aq[i][j] = ((Aq[i][j] - factor * Aq[r][j]) % q + q) % q;
                        bq[i]    = ((bq[i] - factor * bq[r]) % q + q) % q;
                    }

                    bq[i] = (bq[i] - factor * bq[r]) % q;
                    if (bq[i] < 0) bq[i] += q;
                }
            }

            r++;
        }

        vector<mpz_class> logs_q(n, 0);
        for (int col = 0; col < n; col++) {
            if (pivot_col[col] != -1)
                logs_q[col] = bq[pivot_col[col]];
        }

        solutions_per_mod.push_back(logs_q);
    }

    vector<mpz_class> logs(n);

    for (int i = 0; i < n; i++) {
        vector<mpz_class> residues;
        for (auto& sol : solutions_per_mod)
            residues.push_back(sol[i]);

        logs[i] = CRT(residues, moduli);
    }

    return logs;
}

int ComputeFactorBaseBound(const mpz_class& n) {
    double ln_n = mpz_sizeinbase(n.get_mpz_t(), 2) * log(2.0);
    double ln_ln_n = log(ln_n);
    double B = 3.38 * exp(0.5 * sqrt(ln_n * ln_ln_n));
    if (B < 50) B = 50;
    if (B > 50000) B = 50000;

    return (int)B;
}


void solve_worker(IndexCalculus* ic, const mpz_class& b, const vector<mpz_class>& logs, atomic<bool>& done, mpz_class& result, mutex& mtx){
    gmp_randclass rng(gmp_randinit_mt);
    random_device rd;
    rng.seed(rd());

    mpz_class order = ic->p - 1;

    while (!done) {
        mpz_class k = rng.get_z_range(order - 1) + 1;

        mpz_class temp, val;
        mpz_powm(temp.get_mpz_t(), ic->a.get_mpz_t(), k.get_mpz_t(), ic->p.get_mpz_t());

        val = (b * temp) % ic->p;

        vector<int> exps;
        if (ic->isSmooth(val, exps)) {

            mpz_class x = 0;
            bool all_known = true;
            for (size_t i = 0; i < exps.size(); i++){
                x += exps[i] * logs[i];
            }

            x -= k;
            x %= order;
            if (x < 0) x += order;

            lock_guard<mutex> lock(mtx);
            if (!done.load()) {
                result = x;
                done = true;
            }
        }
    }
}

mpz_class IndexCalculus::solve(const mpz_class& b){
    atomic<bool> done(false);
    mpz_class result;
    mutex res_mtx;

    buildFactorBase(ComputeFactorBaseBound(p));
    collectRelations(3 * factor_base.size());

    auto logs = solveLinearSystem();

    int T = thread::hardware_concurrency();
    if (T == 0) T = 4;

    vector<thread> threads;

    for (int i = 0; i < T; i++) {
        threads.emplace_back(
            solve_worker,
            this,
            cref(b),
            cref(logs),
            ref(done),
            ref(result),
            ref(rel_mtx)
        );
    }

    for (auto& t : threads) t.join();

    return result;
}


int main() {
    mpz_class p("131421701276962801");
    mpz_class a("20774904390137831");
    mpz_class b("9890141120090379");

    //mpz_class p = 97;
    //mpz_class a = 5;
    //mpz_class b = 11;

    IndexCalculus ic(p, a);

    cout << "p = " << p << "\n";
    cout << "a = " << a << "\n";
    cout << "b = " << b << "\n\n";

    mpz_class x = ic.solve(b);

    cout << "Result x = " << x << "\n";

    mpz_class check;
    mpz_powm(check.get_mpz_t(), a.get_mpz_t(), x.get_mpz_t(), p.get_mpz_t());

    cout << "Verification: a^x mod p = " << check << "\n";

    if (check == b)
        cout << "Correct\n";
    else
        cout << "Incorrect\n";

    return 0;
}

