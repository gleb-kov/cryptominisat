#ifndef CRYPTOMINISAT5_GENETIC_H
#define CRYPTOMINISAT5_GENETIC_H

#include <cstdint>
#include <cstdio>
#include <limits>
#include <vector>
#include "MersenneTwister.h"
#include "cryptominisat5/solvertypesmini.h"

namespace CMSat {

class Solver;

class GeneticSAT
{
   public:
    lbool main();
    GeneticSAT(Solver* _solver);
    ~GeneticSAT();

   private:
    // void crossover();
    // void nextGeneration();

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

#endif //CRYPTOMINISAT5_GENETIC_H
