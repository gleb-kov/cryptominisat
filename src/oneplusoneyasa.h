#ifndef CRYPTOMINISAT5_ONEPLUSONEYASA_H
#define CRYPTOMINISAT5_ONEPLUSONEYASA_H

#include <cstdint>
#include <cstdio>
#include <limits>
#include <vector>
#include "MersenneTwister.h"
#include "cryptominisat5/solvertypesmini.h"

namespace CMSat {

class Solver;

class OnePlusOneYasaSAT
{
   public:
    lbool main();
    OnePlusOneYasaSAT(Solver* _solver);
    ~OnePlusOneYasaSAT();

   private:
    void large_mutation();
    void small_mutation();

   private:
    constexpr static long double beta = 3.0l; // 3.0 is proven best
    long double normalization = 0;            // aka C^beta_{n/2}
    std::vector<long double> distribution;    // aka P_lambda
    constexpr static uint64_t lambda = 1;     // (1+lambda)-EA
    static constexpr uint64_t cutoff = 100;

   private:
    Solver* solver = nullptr;

    uint32_t lowestbad = std::numeric_limits<uint32_t>::max();
    std::vector<bool> Assigns; /* value of each var */
    std::vector<bool> Best_assigns;
    uint32_t numfalse = 0; /* number of false clauses */
    uint32_t numclauses = 0;
    uint32_t numliterals = 0;

    uint32_t* numtruelit = nullptr; /* number of true literals in each clause */
    Lit* storebase = nullptr;       //all the literals of all the clauses
    Lit** clause = nullptr;         /* clauses to be satisfied */
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
    bool init_problem();
    void init_for_round();

    void pickflips();
    void flipvar(uint32_t varIdx);

    enum class add_cl_ret { added_cl, skipped_cl, unsat };
    template <class T>
    add_cl_ret add_this_clause(const T& cl, uint32_t& i, uint32_t& storeused);

   private:
    inline bool value(const Lit l) const
    {
        return Assigns[l.var()] ^ l.sign();
    }
};

} // namespace CMSat

#endif //CRYPTOMINISAT5_ONEPLUSONEYASA_H
