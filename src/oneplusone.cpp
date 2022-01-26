#include "oneplusone.h"
#include "solver.h"
#include <random>

using namespace CMSat;

OnePlusOneSAT::OnePlusOneSAT(Solver* _solver) :
    solver(_solver)
{
}

OnePlusOneSAT::~OnePlusOneSAT()
{
    free(storebase);
    free(clause);
    free(clsize);
    free(numtruelit);
    free(occur_list_alloc);
    free(occurrence);
    free(numoccurrence);
}

lbool OnePlusOneSAT::main()
{
    if (!init_problem()) {
        //it's actually l_False under assumptions
        //but we'll set the real SAT solver deal with that
        if (solver->conf.verbosity) {
            cout << "c [oneplusone] problem UNSAT under assumptions, returning to main solver"
            << endl;
        }
        return l_Undef;
    }

    // distribution must be divided by normalization, but it isnt, to so tiny float numbers work better
    for (size_t i = 1; i <= solver->nVars() / 2; ++i) {
        distribution[i - 1] = 1.0l / std::pow(i, beta);
        normalization += distribution[i - 1];
    }
    mtrand.seed(solver->mtrand.randInt());

    for (size_t i = 0; i < cutoff; ++i) {
        large_mutation();
        small_mutation();
    }

    if (numfalse == 0 || solver->conf.sls_get_phase) {
        if (solver->conf.verbosity) {
            if (solver->conf.sls_get_phase) {
                cout << "c [oneplusone] saving solution as requested"  << endl;
            } else if (numfalse == 0) {
                cout << "c [oneplusone] ASSIGNMENT FOUND"  << endl;
            }
        }

        for(size_t i = 0; i < solver->nVars(); i++) {
            solver->varData[i].polarity = Best_assigns[i];
        }
    }

    return l_Undef;
}

void OnePlusOneSAT::large_mutation()
{
    //all assumed and already set variables have been removed
    //from the problem already, so the stuff below is safe.
    for (size_t j = 0; j < solver->nVars(); j++) {
        Assigns[j] = mtrand.randInt(1) != 0;
    }
}

void OnePlusOneSAT::small_mutation()
{
    bool updated = false;
    init_for_round();

    for (uint64_t i = 0; i < lambda; ++i) {
        uint32_t flipsCnt = countVarsToFlip();
        pickflips(flipsCnt);

        if (numfalse <= lowestbad) {
            updated = true;
            lowestbad = numfalse;
            Best_assigns = Assigns;
        }
    }

    if (!updated) {
        Assigns = Best_assigns;
    }
}

void OnePlusOneSAT::flipvar(uint32_t toflip)
{
    Lit toenforce = Lit(toflip, Assigns[toflip]);
    Assigns[toflip] = !Assigns[toflip];

    //True made into False
    for (uint32_t i = 0; i < numoccurrence[(~toenforce).toInt()]; i++) {
        uint32_t cli = occurrence[(~toenforce).toInt()][i];

        assert(numtruelit[cli] > 0);
        numtruelit[cli]--;
        if (numtruelit[cli] == 0) {
            numfalse++;
        }
    }

    //made into TRUE
    for (uint32_t i = 0; i < numoccurrence[toenforce.toInt()]; i++) {
        uint32_t cli = occurrence[toenforce.toInt()][i];

        numtruelit[cli]++;
        if (numtruelit[cli] == 1) {
            assert(numfalse > 0);
            numfalse--;
        }
    }
}

void OnePlusOneSAT::init_for_round()
{
    numfalse = 0;

    /* initialize truth assignment and changed time */
    for (uint32_t i = 0; i < numclauses; i++) {
        numtruelit[i] = 0;
    }

    for (uint32_t i = 0; i < numclauses; i++) {
        uint32_t sz = clsize[i];
        assert(sz >= 1);
        for (uint32_t j = 0; j < sz; j++) {
            if (value(clause[i][j])) {
                numtruelit[i]++;
            }
        }
        if (numtruelit[i] == 0) {
            numfalse++;
        }
    }
}

uint32_t OnePlusOneSAT::countVarsToFlip()
{
    static std::mt19937 gen(mtrand.randInt());
    static std::uniform_real_distribution<long double> uniDist(0.0l, normalization);

    size_t toFlip = 0;
    long double weight = uniDist(gen);
    while (toFlip < distribution.size() && 0.0l < weight) {
        weight -= distribution[toFlip];
        ++toFlip;
    }
    return toFlip;
}

void OnePlusOneSAT::pickflips(uint32_t flipsCnt)
{
    // mutation rate = toFlip / solver->nVars()
    // chance of getting the same varIdx twice is negligible
    for (uint32_t i = 0; i < flipsCnt; ++i) {
        uint32_t varIdx = mtrand.randInt(solver->nVars() - 1);
        flipvar(varIdx);
    }
}

template<class T>
OnePlusOneSAT::add_cl_ret OnePlusOneSAT::add_this_clause(const T& cl, uint32_t& i, uint32_t& storeused) {
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
            cout << "c [oneplusone] UNSAT because of assumptions in clause: " << cl << endl;
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

bool OnePlusOneSAT::init_problem()
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

    Assigns.assign(solver->nVars(), true);
    Best_assigns.assign(solver->nVars(), true);
    distribution.resize(solver->nVars() / 2);

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
            cout << "ERROR: Oneplusone -- allocating occurrence lists is wrong" << endl;
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
