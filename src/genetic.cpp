#include "genetic.h"
#include "solver.h"
#include <random>

using namespace CMSat;

GeneticSAT::GeneticSAT(Solver* _solver) :
    solver(_solver)
{
}

GeneticSAT::~GeneticSAT()
{
    free(storebase);
    free(clause);
    free(clsize);
    free(numtruelit);
    free(occur_list_alloc);
    free(occurrence);
    free(numoccurrence);
}

lbool GeneticSAT::main()
{
    if (!init_problem()) {
        //it's actually l_False under assumptions
        //but we'll set the real SAT solver deal with that
        if (solver->conf.verbosity) {
            cout << "c [genetic] problem UNSAT under assumptions, returning to main solver"
                 << endl;
        }
        return l_Undef;
    }

    mtrand.seed(solver->mtrand.randInt());

    std::cout << "GENETIC SAT START" << std::endl;

    std::set<std::pair<size_t, size_t>> scoreOrdering; // score -> index in activeGeneration
    size_t scoreSum = 0;

    for (size_t i = 0; i < generationSize; ++i) {
        for (size_t j = 0; j < solver->nVars(); ++j) {
            activeGeneration[i][j] = mtrand.randInt(1) != 0;
        }
        size_t score = calculate_score(activeGeneration[i]);
        scores[i] = score;
        scoreSum += score;
        scoreOrdering.insert({score, i});
    }

    for (uint32_t genId = 0; genId < generationCount; ++genId) {
        std::vector<std::vector<bool>> newGeneration(generationSize);
        std::vector<size_t> newScores(generationSize);
        std::set<std::pair<size_t, size_t>> newScoreOrdering;
        size_t newScoreSum = 0;

        for (size_t i = 0; i < generationSize - takenBestCount; ++i) {
            const size_t lind = pickMutationPlayer(scoreSum);
            const size_t rind = pickMutationPlayer(scoreSum);

            std::vector<bool> lhs = activeGeneration[lind];
            std::vector<bool> rhs = activeGeneration[rind];

            two_point_crossover(lhs, rhs);
            const size_t lhsScore = calculate_score(lhs);
            const size_t rhsScore = calculate_score(rhs);

            if (lhsScore > rhsScore) {
                newGeneration[i] = std::move(rhs);
                newScores[i] = rhsScore;
                newScoreOrdering.insert({rhsScore, i});
                newScoreSum += rhsScore;
            } else {
                newGeneration[i] = std::move(lhs);
                newScores[i] = lhsScore;
                newScoreOrdering.insert({lhsScore, i});
                newScoreSum += lhsScore;
            }
        }

        auto it = scoreOrdering.begin();
        for (size_t i = 1; i <= takenBestCount; ++i) {
            newGeneration[generationSize - i] = std::move(activeGeneration[it->second]);
            newScores[generationSize - i] = it->first;
            newScoreOrdering.insert({it->first, generationSize - i});
            newScoreSum += it->first;
            ++it;
        }

        activeGeneration = std::move(newGeneration);
        scores = std::move(newScores);
        scoreOrdering = std::move(newScoreOrdering);
        scoreSum = newScoreSum;
    }

    const auto& bestMutationInfo = *scoreOrdering.begin();

    if (bestMutationInfo.first == 0 || solver->conf.sls_get_phase) {
        if (solver->conf.verbosity) {
            if (solver->conf.sls_get_phase) {
                cout << "c [genetic] saving solution as requested"  << endl;
            } else if (bestMutationInfo.first == 0) {
                cout << "c [genetic] ASSIGNMENT FOUND"  << endl;
            }
        }

        for(size_t i = 0; i < solver->nVars(); i++) {
            solver->varData[i].polarity = activeGeneration[bestMutationInfo.second][i];
        }
    }

    return l_Undef;
}

size_t GeneticSAT::calculate_score(const std::vector<bool>& assigns) const
{
    size_t numfalse = 0;

    /* initialize truth assignment and changed time */
    for (uint32_t i = 0; i < numclauses; i++) {
        numtruelit[i] = 0;
    }

    for (uint32_t i = 0; i < numclauses; i++) {
        uint32_t sz = clsize[i];
        assert(sz >= 1);
        for (uint32_t j = 0; j < sz; j++) {
            const auto& literal = clause[i][j];
            if (assigns[literal.var()] ^ literal.sign()) {
                numtruelit[i]++;
            }
        }
        if (numtruelit[i] == 0) {
            numfalse++;
        }
    }

    return numfalse;
}

template<class T>
GeneticSAT::add_cl_ret GeneticSAT::add_this_clause(const T& cl, uint32_t& i, uint32_t& storeused) {
    uint32_t sz = 0;
    bool sat = false;
    for(size_t i3 = 0; i3 < cl.size(); i3++) {
        Lit lit = cl[i3];
        assert(solver->varData[lit.var()].removed == Removed::none);
        lbool val;
        if (solver->value(lit) != l_Undef) {
            val = solver->value(lit);
        } else {
            val = solver->lit_inside_assumptions(lit);
        }

        if (val == l_True) {
            //clause is SAT, skip!
            sat = true;
            continue;
        } else if (val == l_False) {
            continue;
        }
        storebase[storeused+sz] = lit;
        numoccurrence[lit.toInt()]++;
        sz++;
    }
    if (sat) {
        for(uint32_t i3 = 0; i3 < sz; i3++) {
            Lit lit = storebase[storeused+i3];
            assert(numoccurrence[lit.toInt()] > 0);
            numoccurrence[lit.toInt()]--;
        }
        return add_cl_ret::skipped_cl;
    }
    if (sz == 0) {
        //it's unsat because of assumptions
        if (solver->conf.verbosity) {
            cout << "c [genetic] UNSAT because of assumptions in clause: " << cl << endl;
        }
        return add_cl_ret::unsat;
    }

    clause[i] = storebase + storeused;
    storeused += sz;
    clsize[i] = sz;
    numliterals += sz;
    i++;

    return add_cl_ret::added_cl;
}

bool GeneticSAT::init_problem()
{
    if (solver->check_assumptions_contradict_foced_assignment())
    {
        return false;
    }

    assert(solver->decisionLevel() == 0);
    assert(solver->okay());

    uint32_t i;
    uint32_t j;
    //TODO simplify by the assumptions!
    //Then we will automatically get the right solution if we get one :)

    numclauses = solver->longIrredCls.size() + solver->binTri.irredBins;

    clause = (Lit **)malloc(sizeof(Lit *) * numclauses);
    clsize = (uint32_t *)malloc(sizeof(uint32_t) * numclauses);

    numtruelit = (uint32_t *)malloc(sizeof(uint32_t) * numclauses);
    occurrence = (uint32_t **)malloc(sizeof(uint32_t *) * 2 * solver->nVars());
    numoccurrence = (uint32_t *)malloc(sizeof(uint32_t) * 2 * solver->nVars());

    activeGeneration.resize(generationSize, std::vector<bool>(solver->nVars(), true));
    scores.resize(generationSize, 0);

    numliterals = 0;

    /* Read in the clauses and set number of occurrences of each literal */
    uint32_t storeused = 0;
    for (i = 0; i < 2 * solver->nVars(); i++)
        numoccurrence[i] = 0;

    //where all clauses' literals are
    solver->check_stats();
    uint32_t storesize = solver->litStats.irredLits+solver->binTri.irredBins*2;
    storebase = (Lit *)malloc(storesize*sizeof(Lit));
    i = 0;
    for(size_t i2 = 0; i2 < solver->nVars()*2; i2++) {
        Lit lit = Lit::toLit(i2);
        for(const Watched& w: solver->watches[lit]) {
            if (w.isBin() && !w.red() && lit < w.lit2()) {
                assert(storeused+2 <= storesize);
                vector<Lit> this_clause = {lit, w.lit2()};

                if (add_this_clause(this_clause, i, storeused) == add_cl_ret::unsat) {
                    return false;
                }
            }
        }
    }
    for(ClOffset offs: solver->longIrredCls) {
        const Clause* cl = solver->cl_alloc.ptr(offs);
        assert(!cl->freed());
        assert(!cl->getRemoved());
        assert(storeused+cl->size() <= storesize);

        if (add_this_clause(*cl, i, storeused) == add_cl_ret::unsat) {
            return false;
        }
    }
    numclauses = i;

    /* allocate occurrence lists */
    occur_list_alloc = (uint32_t *)malloc(sizeof(uint32_t) * numliterals);
    i = 0;
    for (uint32_t i2 = 0; i2 < solver->nVars()*2; i2++) {
        const Lit lit = Lit::toLit(i2);
        if (i > numliterals) {
            cout << "ERROR: Genetic -- allocating occurrence lists is wrong" << endl;
            exit(-1);
        }
        occurrence[lit.toInt()] = &(occur_list_alloc[i]);
        i += numoccurrence[lit.toInt()];
        numoccurrence[lit.toInt()] = 0;
    }

    /* Third, fill in the occurrence lists */
    for (i = 0; i < numclauses; i++) {
        uint32_t sz = clsize[i];
        assert(sz >= 1);
        for (j = 0; j < sz; j++) {
            const Lit lit = clause[i][j];
            assert(lit.var() < solver->nVars());

            occurrence[lit.toInt()][numoccurrence[lit.toInt()]] = i;
            numoccurrence[lit.toInt()]++;
        }
    }

    return true;
}

size_t GeneticSAT::pickMutationPlayer(size_t totalScore)
{
    static std::mt19937 gen(mtrand.randInt());
    static std::uniform_real_distribution<long double> uniDist(0.0l, totalScore);

    size_t toFlip = 0;
    long double weight = uniDist(gen);

    while (toFlip + 1 < scores.size() && 0.0l < weight) {
        weight -= scores[toFlip];
        ++toFlip;
    }

    return toFlip;
}

void GeneticSAT::two_point_crossover(std::vector<bool> &lhs, std::vector<bool> &rhs)
{
    size_t lind = mtrand.randInt() % solver->nVars();
    size_t rind = mtrand.randInt() % solver->nVars();
    if (lind > rind) {
        std::swap(lind, rind);
    }
    while (lind < rind) {
        std::swap(lhs[lind], rhs[lind]);
        ++lind;
    }
}