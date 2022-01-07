#include "oneplusone.h"
#include "solver.h"

#include <random>

using namespace CMSat;

OnePlusOneSAT::OnePlusOneSAT(Solver* _solver) :
    solver(_solver)
{
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

    mtrand.seed(solver->mtrand.randInt());

    for (size_t i = 0; i < cutoff; ++i) {
        uint32_t toFlip = countVarsToFlip();
        flipvar(toFlip);

        if (numfalse <= lowestbad) {
            lowestbad = numfalse;
            best_assigns = assigns;
            if (numfalse == 0) {
                break;
            }
        }
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
            solver->varData[i].polarity = best_assigns[i] == l_True;
        }
    }
}

bool OnePlusOneSAT::init_problem()
{
    if (solver->check_assumptions_contradict_foced_assignment())
    {
        return false;
    }

    assigns.assign(solver->nVars(), l_True);
    best_assigns.assign(solver->nVars(), l_True);
    distribution.resize(solver->nVars() / 2);

    // distribution must be divided by normalization, but it isnt, to so tiny float numbers work better
    for (size_t i = 1; i <= solver->nVars() / 2; ++i) {
        distribution[i - 1] = 1.0l / static_cast<long double>(i * i * i); // beta = 3, proven best
        normalization += distribution[i - 1];
    }

    return true;
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

void OnePlusOneSAT::flipvar(uint32_t toflip)
{
    // mutation rate = toFlip / solver->nVars()

    for (size_t i = 0; i < solver->nVars(); ++i) {
        if (mtrand.randInt(solver->nVars() - 1) < toflip) { // verified
            assigns[i] = assigns[i] ^ true;
        }
    }

    // TODO: recalc numfalse

    throw std::runtime_error("oneplusone: not implemented");
}
