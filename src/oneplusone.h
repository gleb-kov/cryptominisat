#ifndef CRYPTOMINISAT5_ONEPLUSONE_H
#define CRYPTOMINISAT5_ONEPLUSONE_H

#include <cstdint>
#include <cstdio>
#include <vector>
#include <limits>
#include "MersenneTwister.h"
#include "cryptominisat5/solvertypesmini.h"

namespace CMSat {

class Solver;

class OnePlusOneSAT
{
   public:
    lbool main();
    OnePlusOneSAT(Solver* _solver);

   private:
    long double normalization = 0; // aka C^beta_{n/2}
    std::vector<long double> distribution; // aka P_lambda

   private:
    Solver* solver = nullptr;
    static constexpr uint64_t cutoff = 100;
    uint32_t lowestbad = std::numeric_limits<uint32_t>::max();
    std::vector<lbool> assigns;         /* value of each var */
    std::vector<lbool> best_assigns;
    uint32_t numfalse = 0;   /* number of false clauses */

    MTRand mtrand;

   private:
    uint32_t countVarsToFlip();
    bool init_problem();
    void flipvar(uint32_t toflip);
};

}

#endif //CRYPTOMINISAT5_ONEPLUSONE_H
