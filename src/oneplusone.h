#ifndef CRYPTOMINISAT5_ONEPLUSONE_H
#define CRYPTOMINISAT5_ONEPLUSONE_H

#include <cstdint>
#include <cstdio>
#include <limits>
#include <vector>
#include "MersenneTwister.h"
#include "cryptominisat5/solvertypesmini.h"

namespace CMSat {

class Solver;

class OnePlusOneSAT
{
   public:
    lbool main();
    OnePlusOneSAT(Solver* _solver);
    ~OnePlusOneSAT();

   private:
    constexpr static long double beta = 3.0l; // 3.0 is proven best
    long double normalization = 0;         // aka C^beta_{n/2}
    std::vector<long double> distribution; // aka P_lambda

   private:
    Solver* solver = nullptr;
    static constexpr uint64_t cutoff = 100;

    uint32_t lowestbad = std::numeric_limits<uint32_t>::max();
    std::vector<lbool> assigns; /* value of each var */
    std::vector<lbool> best_assigns;
    uint32_t numfalse = 0; /* number of false clauses */
    uint32_t numclauses = 0;
    uint32_t numliterals = 0;

    uint32_t* numtruelit = nullptr; /* number of true literals in each clause */
    Lit* storebase = nullptr; //all the literals of all the clauses
    Lit** clause = nullptr;   /* clauses to be satisfied */
    /* indexed as clause[clause_num][literal_num] */
    uint32_t* clsize = nullptr; /* length of each clause */

    ///TODO make this half the size by using offsets
    /** where each literal occurs, size 2*numvars
       indexed as occurrence[literal+numvars][occurrence_num] */
    uint32_t** occurrence = nullptr;
    uint32_t* occur_list_alloc = nullptr;

    /** number of times each literal occurs, size 2*numvars
        indexed as numoccurrence[literal+numvars]              */
    uint32_t* numoccurrence = nullptr;

    MTRand mtrand;

   private:
    uint32_t countVarsToFlip();
    bool init_problem();
    void init_for_round();

    void pickflips(uint32_t flipsCnt);
    void flipvar(uint32_t varIdx);

    enum class add_cl_ret { added_cl, skipped_cl, unsat };
    template <class T>
    add_cl_ret add_this_clause(const T& cl, uint32_t& i, uint32_t& storeused);

   private:
    inline lbool value(const uint32_t var) const {
        return assigns[var];
    }
    inline lbool value(const Lit l) const {
        return assigns[l.var()] ^ l.sign();
    }
};

} // namespace CMSat

#endif //CRYPTOMINISAT5_ONEPLUSONE_H
