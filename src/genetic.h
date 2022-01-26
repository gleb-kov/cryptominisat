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
    static constexpr size_t generationSize = 10;
    static constexpr uint32_t generationCount = 300;
    static constexpr size_t takenBestCount = 2;

   private:
    std::vector<std::vector<bool>> activeGeneration;
    std::vector<size_t> scores;

   private:
    size_t pickMutationPlayer(size_t totalScore);
    void two_point_crossover(std::vector<bool>&, std::vector<bool>&);
    // void nextGeneration();

   private:
    Solver* solver = nullptr;

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
    size_t calculate_score(const std::vector<bool>& assigns) const;

    enum class add_cl_ret { added_cl, skipped_cl, unsat };
    template <class T>
    add_cl_ret add_this_clause(const T& cl, uint32_t& i, uint32_t& storeused);
};

} // namespace CMSat

#endif //CRYPTOMINISAT5_GENETIC_H
