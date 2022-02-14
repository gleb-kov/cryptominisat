/******************************************
Copyright (c) 2018, Henry Kautz <henry.kautz@gmail.com>
Copyright (C) 2009-2020 Authors of CryptoMiniSat, see AUTHORS file <soos.mate@gmail.com>

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
***********************************************/

#include "time_mem.h"
#include <limits>
#include <cstdio>
#include <cmath>
#include <cstdlib>
#include "constants.h"
#include "walksatlm.h"
#include "solver.h"
//#define SLOW_DEBUG

using namespace CMSat;

uint32_t WalkLmSAT::RANDMOD(uint32_t d)
{
    return d > 1 ? mtrand.randInt(d-1) : 0;
}

WalkLmSAT::WalkLmSAT(Solver* _solver) :
    solver(_solver)
{
}

WalkLmSAT::~WalkLmSAT()
{
    free(storebase);
    free(clause);
    free(clsize);

    free(false_cls);
    free(map_cl_to_false_cls);
    free(numtruelit);

    free(occur_list_alloc);
    free(occurrence);
    free(numoccurrence);
    free(assigns);
    free(best_assigns);
    free(breakcount);
    free(make1count);
    free(make2count);
    free(changed);
}

lbool WalkLmSAT::main()
{
    //It might not work well with few number of variables
    //rnovelty could also die/exit(-1), etc.
    if (solver->nVars() < 50) {
        if (solver->conf.verbosity) {
            cout << "c [walksat] too few variables for walksat"
            << endl;
        }
        return l_Undef;
    }
    startTime = cpuTime();
    parse_parameters();
    mtrand.seed(solver->mtrand.randInt());
    print_parameters();
    if (!init_problem()) {
        //it's actually l_False under assumptions
        //but we'll set the real SAT solver deal with that
        if (solver->conf.verbosity) {
            cout << "c [walksat] problem UNSAT under assumptions, returning to main solver"
            << endl;
        }
        return l_Undef;
    }
    initialize_statistics();
    print_statistics_header();

    lowestbad = std::numeric_limits<uint32_t>::max();

    while (!found_solution && numtry < solver->conf.walksat_max_runs) {
        numtry++;
        init_for_round();
        update_statistics_start_try();
        numflip = 0;

        while (!found_solution && (numfalse > 0) && (numflip < cutoff)) {
            numflip++;

            uint32_t var = pickrnovelty();
            flipvar(var);
            update_statistics_end_flip();
        }

        update_and_print_statistics_end_try();
    }
    print_statistics_final();
    return l_Undef;
}

void WalkLmSAT::WalkLmSAT::flipvar(uint32_t toflip)
{
    Lit toenforce;
    uint32_t numocc;
    changed[toflip] = numflip;

    if (assigns[toflip] == l_True)
        toenforce = Lit(toflip, true);
    else
        toenforce = Lit(toflip, false);

    assert(value(toflip) != l_Undef);
    assigns[toflip] = assigns[toflip] ^ true;

    //True made into False
    numocc = numoccurrence[(~toenforce).toInt()];
    for (uint32_t i = 0; i < numocc; i++) {
        uint32_t cli = occurrence[(~toenforce).toInt()][i];

        assert(numtruelit[cli] > 0);
        numtruelit[cli]--;
        if (numtruelit[cli] == 0) {
            false_cls[numfalse] = cli;
            map_cl_to_false_cls[cli] = numfalse;
            numfalse++;
            /* Decrement toflip's breakcount */
            assert(breakcount[toflip] > 0);
            breakcount[toflip]--;

            /* Increment the makecount of all vars in the clause */
            uint32_t sz = clsize[cli];
            Lit* litptr = clause[cli];
            for (uint32_t j = 0; j < sz; j++) {
                Lit lit = *(litptr++);
                make1count[lit.var()]++;
            }

        } else if (numtruelit[cli] == 1) {
            /* Find the lit in this clause that makes it true, and inc its breakcount */
            Lit *litptr = clause[cli];
            for (uint32_t j = 0; j < clsize[cli]; ++j) {
                /* lit = clause[cli][j]; */
                Lit lit = *(litptr++);
                if (value(lit) == l_True) {
                    breakcount[lit.var()]++;

                    /* Swap lit into first position in clause */
                    if ((--litptr) != clause[cli]) {
                        Lit temp = clause[cli][0];
                        clause[cli][0] = *(litptr);
                        *(litptr) = temp;
                    }
                } else {
                    make2count[lit.var()]++;
                }
            }
        }
    }

    //made into TRUE
    numocc = numoccurrence[toenforce.toInt()];
    for (uint32_t i = 0; i < numocc; i++) {
        uint32_t cli = occurrence[toenforce.toInt()][i];

        numtruelit[cli]++;
        if (numtruelit[cli] == 1) {
            assert(numfalse > 0);
            const uint32_t last_false_cl = false_cls[numfalse-1];
            uint32_t position_in_false_cls = map_cl_to_false_cls[cli];
            numfalse--;

            //the postiion in false_cls where this clause was is now replaced with
            //the one at the end
            false_cls[position_in_false_cls] = last_false_cl;

            //update map_cl_to_false_cls of the clause
            map_cl_to_false_cls[last_false_cl] = position_in_false_cls;

            /* Increment toflip's breakcount */
            breakcount[toflip]++;

            /* Decrement the makecount of all vars in the clause */
            uint32_t sz = clsize[cli];
            Lit* litptr = clause[cli];
            for (uint32_t j = 0; j < sz; j++) {
                /* lit = clause[cli][j]; */
                Lit lit = *(litptr++);
                assert(make1count[lit.var()] > 0);
                make1count[lit.var()]--;
            }

        } else if (numtruelit[cli] == 2) {
            /* Find the lit in this clause other than toflip that makes it true,
             * and decrement its breakcount */
            Lit *litptr = clause[cli];
            for (uint32_t j = 0; j < clsize[cli]; ++j) {
                /* lit = clause[cli][j]; */
                Lit lit = *(litptr++);
                if (value(lit) == l_True && (toflip != lit.var())) {
                    assert(breakcount[lit.var()] > 0);
                    breakcount[lit.var()]--;
                } else {
                    make2count[lit.var()]--;
                }
            }
        }
    }
}

void WalkLmSAT::check_make_break() {
    vector<uint32_t> makecount_check(numvars, 0);
    vector<uint32_t> breakcount_check(numvars, 0);
    vector<uint32_t> numtruelit_check(numclauses, 0);
    uint32_t numfalse_check = 0;

    /* Set makecount + breakcount  */
    for (uint32_t i = 0; i < numclauses; i++) {
        Lit thetruelit;
        uint32_t sz = clsize[i];
        assert(sz > 0);
        for (uint32_t j = 0; j < sz; j++) {
            if (value(clause[i][j]) == l_True) {
                thetruelit = clause[i][j];
                numtruelit_check[i]++;
            }
        }
        if (numtruelit_check[i] == 0) {
            numfalse_check++;
            for (uint32_t j = 0; j < clsize[i]; j++) {
                makecount_check[clause[i][j].var()]++;
            }
        } else if (numtruelit_check[i] == 1) {
            breakcount_check[thetruelit.var()]++;
        }
    }

    for(size_t i = 0; i < numvars; i++) {
        assert(breakcount_check[i] == breakcount[i]);
        assert(makecount_check[i] == make1count[i]);
    }

    for(size_t i = 0; i < numclauses; i++) {
        assert(numtruelit_check[i] == numtruelit[i]);
    }
    assert(numfalse == numfalse_check);
}

/************************************/
/* Initialization                   */
/************************************/

void WalkLmSAT::parse_parameters()
{
    numerator = walk_probability * denominator;
}

void WalkLmSAT::init_for_round()
{
    assert(solver->decisionLevel() == 0);
    assert(solver->okay());

    if (adaptive) {
        walk_probability = 0.0;
        numerator = (uint32_t)(walk_probability * denominator);
        stagnation_timer = (uint32_t)(numclauses * adaptive_theta);
        last_adaptive_objective = std::numeric_limits<uint32_t>::max();
    }

    //reset makecount, breakcount and set random starting position
    numfalse = 0;
    for (uint32_t i = 0; i < numvars; i++) {
        breakcount[i] = 0;
        make1count[i] = 0;
        make2count[i] = 0;
        //all assumed and already set variables have been removed
        //from the problem already, so the stuff below is safe.
        assigns[i] = mtrand.randInt(1) ? l_True: l_False;
    }

    /* initialize truth assignment and changed time */
    for (uint32_t i = 0; i < numclauses; i++) {
        numtruelit[i] = 0;
    }

    /* Set makecount + breakcount  */
    for (uint32_t i = 0; i < numclauses; i++) {
        Lit thetruelit = lit_Undef;
        uint32_t sz = clsize[i];
        assert(sz >= 1);
        for (uint32_t j = 0; j < sz; j++) {
            if (value(clause[i][j]) == l_True) {
                numtruelit[i]++;
                thetruelit = clause[i][j];
            }
        }
        if (numtruelit[i] == 0) {
            map_cl_to_false_cls[i] = numfalse;
            false_cls[numfalse] = i;
            numfalse++;
            for (uint32_t j = 0; j < clsize[i]; j++) {
                make1count[clause[i][j].var()]++;
            }
        } else if (numtruelit[i] == 1) {
            breakcount[thetruelit.var()]++;
            for (uint32_t j = 0; j < clsize[i]; j++) {
                if (clause[i][j] != thetruelit) {
                    make2count[clause[i][j].var()]++;
                }
            }
        }
    }

    #ifdef SLOW_DEBUG
    check_make_break();
    #endif
}

template<class T>
WalkLmSAT::add_cl_ret WalkLmSAT::add_this_clause(const T& cl, uint32_t& i, uint32_t& storeused) {
    uint32_t sz = 0;
    bool sat = false;
    for(size_t i3 = 0; i3 < cl.size(); i3++) {
        Lit lit = cl[i3];
        assert(solver->varData[lit.var()].removed == Removed::none);
        lbool val = l_Undef;
        if (solver->value(lit) != l_Undef) {
            val = solver->value(lit);
        } else {
            val = solver->lit_inside_assumptions(lit);
        }

        if (val == l_True) {
            //clause is SAT, skip!
            cl_shortening_triggered = true;
            sat = true;
            continue;
        } else if (val == l_False) {
            cl_shortening_triggered = true;
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
            cout << "c [walksat] UNSAT because of assumptions in clause: " << cl << endl;
        }
        return add_cl_ret::unsat;
    }

    clause[i] = storebase + storeused;
    storeused += sz;
    clsize[i] = sz;
    numliterals += sz;
    longestclause = std::max(longestclause, sz);
    i++;

    return add_cl_ret::added_cl;
}

bool WalkLmSAT::init_problem()
{
    if (solver->check_assumptions_contradict_foced_assignment())
    {
        return false;
    }

    uint32_t i;
    uint32_t j;
    //TODO simplify by the assumptions!
    //Then we will automatically get the right solution if we get one :)

    numvars = solver->nVars();
    numclauses = solver->longIrredCls.size() + solver->binTri.irredBins;

    clause = (Lit **)calloc(sizeof(Lit *), numclauses);
    clsize = (uint32_t *)calloc(sizeof(uint32_t), numclauses);

    //false-true lits
    false_cls = (uint32_t *)calloc(sizeof(uint32_t), numclauses);
    map_cl_to_false_cls = (uint32_t *)calloc(sizeof(uint32_t), numclauses);
    numtruelit = (uint32_t *)calloc(sizeof(uint32_t), numclauses);

    occurrence = (uint32_t **)calloc(sizeof(uint32_t *), (2 * numvars));
    numoccurrence = (uint32_t *)calloc(sizeof(uint32_t), (2 * numvars));
    assigns = (lbool *)calloc(sizeof(lbool), numvars);
    best_assigns = (lbool *)calloc(sizeof(lbool), numvars);
    breakcount = (uint32_t *)calloc(sizeof(uint32_t), numvars);
    changed = (int64_t *)calloc(sizeof(int64_t), numvars);
    make1count = (uint32_t *)calloc(sizeof(uint32_t), numvars);
    make2count = (uint32_t *)calloc(sizeof(uint32_t), numvars);
    occur_list_alloc = NULL;
    for(uint32_t i2 = 0; i2 < numvars; i2 ++) {
        /* ties in age between unchanged variables broken for lowest-numbered */
        changed[i2] = 0-(int32_t)i2-1000;
    }

    numliterals = 0;
    longestclause = 0;

    /* Read in the clauses and set number of occurrences of each literal */
    uint32_t storeused = 0;
    for (i = 0; i < 2 * numvars; i++)
        numoccurrence[i] = 0;

    //where all clauses' literals are
    vector<Lit> this_clause;
    solver->check_stats();
    uint32_t storesize = solver->litStats.irredLits+solver->binTri.irredBins*2;
    storebase = (Lit *)malloc(storesize*sizeof(Lit));
    i = 0;
    for(size_t i2 = 0; i2 < solver->nVars()*2; i2++) {
        Lit lit = Lit::toLit(i2);
        for(const Watched& w: solver->watches[lit]) {
            if (w.isBin() && !w.red() && lit < w.lit2()) {
                assert(storeused+2 <= storesize);
                this_clause.clear();
                this_clause.push_back(lit);
                this_clause.push_back(w.lit2());

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
    assert(storeused == storesize || (cl_shortening_triggered && storeused < storesize));
    assert(i == numclauses || (cl_shortening_triggered && i < numclauses));
    numclauses = i;

    /* allocate occurence lists */
    occur_list_alloc = (uint32_t *)calloc(sizeof(uint32_t), numliterals);
    i = 0;
    for (uint32_t i2 = 0; i2 < numvars*2; i2++) {
        const Lit lit = Lit::toLit(i2);
        if (i > numliterals) {
            cout << "ERROR: Walksat -- allocating occurrence lists is wrong" << endl;
            exit(-1);
        }
        occurrence[lit.toInt()] = &(occur_list_alloc[i]);
        i += numoccurrence[lit.toInt()];
        numoccurrence[lit.toInt()] = 0;
    }
    assert(i == numliterals || (cl_shortening_triggered && i < numliterals));

    /* Third, fill in the occurence lists */
    for (i = 0; i < numclauses; i++) {
        uint32_t sz = clsize[i];
        assert(sz >= 1);
        for (j = 0; j < sz; j++) {
            const Lit lit = clause[i][j];
            assert(lit.var() < numvars);

            occurrence[lit.toInt()][numoccurrence[lit.toInt()]] = i;
            numoccurrence[lit.toInt()]++;
        }
    }

    #ifdef SLOW_DEBUG
    check_num_occurs();
    #endif

    return true;
}

/************************************/
/* Printing and Statistics          */
/************************************/

void WalkLmSAT::print_parameters()
{
    if (solver->conf.verbosity) {
        cout << "c [walksat] Mate Soos, based on WALKSAT v56 by Henry Kautz" << endl;
        cout << "c [walksat] cutoff = %" << cutoff << endl;
        cout << "c [walksat] tries = " << solver->conf.walksat_max_runs << endl;
        cout << "c [walksat] walk probabability = "
        << std::fixed << std::setprecision(2) << walk_probability << endl;
    }
}

void WalkLmSAT::initialize_statistics()
{
    x = 0;
    r = 0;
    tail_start_flip = tail * numvars;

    if (solver->conf.verbosity) {
        cout << "c [walksat] tail starts after flip = " << tail_start_flip << endl;
    }
}

void WalkLmSAT::print_statistics_header()
{
    if (solver->conf.verbosity) {
        cout << "c [walksat] numvars = " << numvars << ", numclauses = "
        << numclauses << ", numliterals = " << numliterals << endl;

        cout << "c [walksat]    lowbad    unsat        avg    flips    nume-" << endl;
        cout << "c [walksat]      this      end      unsat     this    rator" << endl;
        cout << "c [walksat]       try      try       tail      try         " << endl;
    }
}

void WalkLmSAT::update_statistics_start_try()
{
    lowbad = numfalse;
    sample_size = 0;
    sumfalse = 0.0;
}

void WalkLmSAT::update_statistics_end_flip()
{
    if (adaptive) {
        /* Reference for adaptie noise option:
         * An Adaptive Noise Mechanism for WalkLmSAT (Corrected). Holger H. Hoos.
         */

        if (numfalse < last_adaptive_objective) {
            last_adaptive_objective = numfalse;
            stagnation_timer = (int)(numclauses * adaptive_theta);
            /* p = p - p * (phi)/2
               p = (1 - phi/2) * p
               p = (1 - phi/2) * (numerator / denominator)
               p (denominator) = (1 - phi/2) * numerator
               numerator = (1 - phi/2) * numerator
            */
            numerator = (int)((1.0 - adaptive_phi / 2.0) * numerator);
        } else {
            stagnation_timer = stagnation_timer - 1;
            if (stagnation_timer <= 0) {
                last_adaptive_objective = numfalse;
                stagnation_timer = (int)(numclauses * adaptive_theta);
                /* p = p + (1 - p) * phi
                 * denominator * p = denominator * p + denominator * (1 - p) * phi
                 * numerator = numerator + denominator * (1 - p) * phi;
                 * numerator = numerator + denominator * (1 - numerator/denominator) * phi;
                 * numerator = numerator + (denominator - numerator) * phi;
                 */
                numerator = numerator + (int)((denominator - numerator) * adaptive_phi);
            }
        }
    }

    if (numfalse < lowbad) {
        lowbad = numfalse;
    }
    if (numfalse < lowestbad) {
        lowestbad = numfalse;
        for(uint32_t i = 0; i < numvars; i++) {
            best_assigns[i] = assigns[i];
        }

    }
    if (numflip >= tail_start_flip) {
        sumfalse += numfalse;
        sample_size++;
    }
}

void WalkLmSAT::update_and_print_statistics_end_try()
{
    totalflip += numflip;
    x += numflip;
    r++;

    if (sample_size > 0) {
        avgfalse = sumfalse / sample_size;

        sum_avgfalse += avgfalse;
        number_sampled_runs += 1;

        if (numfalse == 0) {
            suc_number_sampled_runs += 1;
            suc_sum_avgfalse += avgfalse;
        } else {
            nonsuc_number_sampled_runs += 1;
            nonsuc_sum_avgfalse += avgfalse;
        }
    } else {
        avgfalse = 0;
    }

    if (numfalse == 0) {
        found_solution = true;
        totalsuccessflip += numflip;
        integer_sum_x += x;
        sum_x = (double)integer_sum_x;
        sum_r += r;
        x = 0;
        r = 0;
    }

    if (solver->conf.verbosity) {
        cout
        << "c [walksat] "
        << std::right
        << std::setw(9) << lowbad
        << std::setw(9) << numfalse
        << std::setw(9+2) << avgfalse
        << std::setw(9) << numflip
        << std::setw(9) << numerator
        << endl;
    }

    if (numfalse == 0 && countunsat() != 0) {
        cout << "ERROR: WalkLmSAT -- verification of solution fails!" << endl;
        exit(-1);
    }
}

void WalkLmSAT::print_statistics_final()
{
    totalTime = cpuTime() - startTime;
    seconds_per_flip = ratio_for_stat(totalTime, totalflip);
    if (solver->conf.verbosity) {
        cout << "c [walksat] total elapsed seconds = " <<  totalTime << endl;
        cout << "c [walksat] num tries: " <<  numtry  << endl;
        cout << "c [walksat] avg flips per second = " << ratio_for_stat(totalflip, totalTime) << endl;
        cout << "c [walksat] final success rate = " << stats_line_percent(1, numtry)  << endl;
        cout << "c [walksat] avg length successful tries = %" << totalsuccessflip << endl;
        if (found_solution) {
            cout << "c [walksat] total success flip = " << totalsuccessflip << endl;
            cout << "c [walksat] flips = " << totalflip << endl;
            cout << "c [walksat] flips until assign = " << sum_x << endl;
            cout << "c [walksat] restarts until assign = " << sum_r << endl;
        }
    }

    if (number_sampled_runs) {
        mean_avgfalse = sum_avgfalse / number_sampled_runs;

        if (suc_number_sampled_runs) {
            suc_mean_avgfalse = suc_sum_avgfalse / suc_number_sampled_runs;
        } else {
            suc_mean_avgfalse = 0;
        }

        if (nonsuc_number_sampled_runs) {
            nonsuc_mean_avgfalse = nonsuc_sum_avgfalse / nonsuc_number_sampled_runs;
        } else {
            nonsuc_mean_avgfalse = 0;
        }

        if (solver->conf.verbosity) {
            cout << "c [walksat] final numbad level statistics"  << endl;
            cout << "c [walksat]     statistics over all runs:"  << endl;
            cout << "c [walksat]       overall mean avg numbad = " << mean_avgfalse << endl;
            cout << "c [walksat]     statistics on successful runs:"  << endl;
            cout << "c [walksat]       successful mean avg numbad = " << suc_mean_avgfalse << endl;
            cout << "c [walksat]     statistics on nonsuccessful runs:"  << endl;
            cout << "c [walksat]       nonsuccessful mean avg numbad level = " << nonsuc_mean_avgfalse  << endl;
        }
    }

    if (!found_solution) {
        if (solver->conf.verbosity >=2) {
            cout << "c [walksat] ASSIGNMENT NOT FOUND"  << endl;
        }
    }

    if (found_solution || solver->conf.sls_get_phase) {
        if (solver->conf.verbosity) {
            if (solver->conf.sls_get_phase) {
                cout << "c [walksat] saving solution as requested"  << endl;
            } else if (found_solution) {
                cout << "c [walksat] ASSIGNMENT FOUND"  << endl;
            }
        }

        for(size_t i = 0; i < solver->nVars(); i++) {
            solver->varData[i].polarity = best_assigns[i] == l_True;
        }
    }
}

/*******************************************************/
/* Utility Functions                                   */
/*******************************************************/
//ONLY used for checking solution
uint32_t WalkLmSAT::countunsat()
{
    uint32_t unsat = 0;
    for (uint32_t i = 0; i < numclauses; i++) {
        bool bad = true;
        for (uint32_t j = 0; j < clsize[i]; j++) {
            Lit lit = clause[i][j];
            if (value(lit) == l_True) {
                bad = false;
                break;
            }
        }
        if (bad) {
            unsat++;
        }
    }
    return unsat;
}

void WalkLmSAT::check_num_occurs()
{
    vector<uint32_t> n_occur;
    n_occur.resize(numvars*2, 0);
    for (uint32_t i = 0; i < numclauses; i++) {
        uint32_t sz = clsize[i];
        assert(sz >= 1);
        for (uint32_t j = 0; j < sz; j++) {
            Lit lit = clause[i][j];
            n_occur[lit.toInt()]++;
        }
    }
    for (uint32_t i = 0; i < n_occur.size(); i++) {
        assert(n_occur[i] == numoccurrence[i]);
    }

    /* Check every lit in the occurence lists */
    for (uint32_t i = 0; i < numvars*2; i++) {
        Lit lit = Lit::toLit(i);
        for (uint32_t j = 0; j < numoccurrence[lit.toInt()]; j++) {
            uint32_t clnum = occurrence[lit.toInt()][j];
            Lit* cl = clause[clnum];
            uint32_t sz = clsize[clnum];
            bool found = false;
            for(uint32_t k = 0; k < sz; k++) {
                if (cl[k] == lit) {
                    found = true;
                }
            }
            assert(found);
        }
    }
}

/****************************************************************/
/*                  Heuristics                                  */
/****************************************************************/

uint32_t WalkLmSAT::pickrnovelty()
{
    uint32_t tofix = false_cls[RANDMOD(numfalse)];
    uint32_t clausesize = clsize[tofix];
    if (clausesize == 1) {
        return clause[tofix][0].var();
    }

    uint32_t bestVar = clause[tofix][0].var();

    for (uint32_t i = 0; i < clausesize; i++) {
        uint32_t var = clause[tofix][i].var();
        uint32_t lmake = 3 * make1count[var] + 2 * make2count[var];
        uint32_t lmakeBest = 3 * make1count[bestVar] + 2 * make2count[bestVar];
        if (breakcount[var] < breakcount[bestVar]) {
            bestVar = var;
        } else if (breakcount[var] == breakcount[bestVar] && lmake > lmakeBest) {
            bestVar = var;
        }
    }

    if (breakcount[bestVar] != 0 && RANDMOD(1000) <= noise * 1000) {
        return clause[tofix][RANDMOD(clausesize)].var();
    } else {
        return bestVar;
    }
}
