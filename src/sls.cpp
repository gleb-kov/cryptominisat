/******************************************
Copyright (C) 2009-2020 Authors of CryptoMiniSat, see AUTHORS file

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

#include "sls.h"
#include "solver.h"
#ifdef USE_YALSAT
#include "yalsat.h"
#endif
#include "walksat.h"
#include "walksatlm.h"
#include "walksatmvt.h"
#include "ccnr_cms.h"
#include "oneplusone.h"
#include "oneplusonefea.h"
#include "oneplusonefeaup.h"
#include "oneplusoneyasa.h"
#include "genetic.h"

using namespace CMSat;

SLS::SLS(Solver* _solver) :
    solver(_solver)
{}

SLS::~SLS()
{}

lbool SLS::run(const uint32_t num_sls_called)
{
    if (solver->conf.which_sls == "yalsat") {
#ifdef USE_YALSAT
        return run_yalsat();
#else
        cout << "ERROR: yalsat was not compiled in. Set -DREQUIRE_YALSAT=ON" << endl;
        exit(-1);
#endif
    } else if (solver->conf.which_sls == "ccnr") {
        return run_ccnr(num_sls_called);
    } else if (solver->conf.which_sls == "walksat") {
        return run_walksat();
    } else if (solver->conf.which_sls == "walksatlm") {
        return run_walksatlm();
    } else if (solver->conf.which_sls == "walksatmvt") {
        return run_walksatmvt();
    } else if (solver->conf.which_sls == "oneplusone") {
        return run_oneplusone();
    } else if (solver->conf.which_sls == "oneplusonefea") {
        return run_oneplusonefea();
    } else if (solver->conf.which_sls == "oneplusonefeaup") {
        return run_oneplusonefeaup();
    } else if (solver->conf.which_sls == "oneplusoneyasa") {
        return run_oneplusoneyasa();
    } else if (solver->conf.which_sls == "genetic") {
        return run_genetic();
    } else if (solver->conf.which_sls == "ccnr_yalsat") {
        if ((num_sls_called % 2) == 0) {
            return run_ccnr(num_sls_called);
        } else {
            #ifdef USE_YALSAT
            return run_yalsat();
            #else
            cout << "ERROR: yalsat was not compiled in. Set -DREQUIRE_YALSAT=ON" << endl;
            exit(-1);
            #endif
        }
    } else {
        cout << "ERROR: SLS configuration '" << solver->conf.which_sls
        << "' does not exist. Only 'yalsat', 'walksat', 'walksatmvt', 'oneplusonefea', 'oneplusonefeaup', 'genetic' are acceptable."
        << endl;
        exit(-1);
    }
}

lbool SLS::run_walksat()
{
    WalkSAT walksat(solver);
    double mem_needed_mb = (double)approx_mem_needed()/(1000.0*1000.0);
    double maxmem = solver->conf.sls_memoutMB*solver->conf.var_and_mem_out_mult;
    if (mem_needed_mb < maxmem) {
        lbool ret = walksat.main();
        return ret;
    }

    if (solver->conf.verbosity) {
        cout << "c [sls] would need "
             << std::setprecision(2) << std::fixed << mem_needed_mb
             << " MB but that's over limit of " << std::fixed << maxmem
             << " MB -- skipping" << endl;
    }

    return l_Undef;
}

lbool SLS::run_walksatlm()
{
    WalkLmSAT walksat(solver);
    double mem_needed_mb = (double)approx_mem_needed()/(1000.0*1000.0);
    double maxmem = solver->conf.sls_memoutMB*solver->conf.var_and_mem_out_mult;
    if (mem_needed_mb < maxmem) {
        lbool ret = walksat.main();
        return ret;
    }

    if (solver->conf.verbosity) {
        cout << "c [sls] would need "
             << std::setprecision(2) << std::fixed << mem_needed_mb
             << " MB but that's over limit of " << std::fixed << maxmem
             << " MB -- skipping" << endl;
    }

    return l_Undef;
}

lbool SLS::run_walksatmvt()
{
    WalkMvtSAT walksat(solver);
    double mem_needed_mb = (double)approx_mem_needed()/(1000.0*1000.0);
    double maxmem = solver->conf.sls_memoutMB*solver->conf.var_and_mem_out_mult;
    if (mem_needed_mb < maxmem) {
        lbool ret = walksat.main();
        return ret;
    }

    if (solver->conf.verbosity) {
        cout << "c [sls] would need "
        << std::setprecision(2) << std::fixed << mem_needed_mb
        << " MB but that's over limit of " << std::fixed << maxmem
        << " MB -- skipping" << endl;
    }

    return l_Undef;
}

lbool SLS::run_oneplusone()
{
    OnePlusOneSAT oneplusone(solver);
    double mem_needed_mb = (double)approx_mem_needed()/(1000.0*1000.0);
    double maxmem = solver->conf.sls_memoutMB*solver->conf.var_and_mem_out_mult;
    if (mem_needed_mb < maxmem) {
        lbool ret = oneplusone.main();
        return ret;
    }

    if (solver->conf.verbosity) {
        cout << "c [sls] would need "
             << std::setprecision(2) << std::fixed << mem_needed_mb
             << " MB but that's over limit of " << std::fixed << maxmem
             << " MB -- skipping" << endl;
    }

    return l_Undef;
}

lbool SLS::run_oneplusonefea()
{
    OnePlusOneFeaSAT oneplusone(solver);
    double mem_needed_mb = (double)approx_mem_needed()/(1000.0*1000.0);
    double maxmem = solver->conf.sls_memoutMB*solver->conf.var_and_mem_out_mult;
    if (mem_needed_mb < maxmem) {
        lbool ret = oneplusone.main();
        return ret;
    }

    if (solver->conf.verbosity) {
        cout << "c [sls] would need "
             << std::setprecision(2) << std::fixed << mem_needed_mb
             << " MB but that's over limit of " << std::fixed << maxmem
             << " MB -- skipping" << endl;
    }

    return l_Undef;
}

lbool SLS::run_oneplusonefeaup()
{
    OnePlusOneFeaUnitPropSAT oneplusone(solver);
    double mem_needed_mb = (double)approx_mem_needed()/(1000.0*1000.0);
    double maxmem = solver->conf.sls_memoutMB*solver->conf.var_and_mem_out_mult;
    if (mem_needed_mb < maxmem) {
        lbool ret = oneplusone.main();
        return ret;
    }

    if (solver->conf.verbosity) {
        cout << "c [sls] would need "
             << std::setprecision(2) << std::fixed << mem_needed_mb
             << " MB but that's over limit of " << std::fixed << maxmem
             << " MB -- skipping" << endl;
    }

    return l_Undef;
}

lbool SLS::run_oneplusoneyasa() {
    OnePlusOneYasaSAT oneplusone(solver);
    double mem_needed_mb = (double)approx_mem_needed()/(1000.0*1000.0);
    double maxmem = solver->conf.sls_memoutMB*solver->conf.var_and_mem_out_mult;
    if (mem_needed_mb < maxmem) {
        lbool ret = oneplusone.main();
        return ret;
    }

    if (solver->conf.verbosity) {
        cout << "c [sls] would need "
             << std::setprecision(2) << std::fixed << mem_needed_mb
             << " MB but that's over limit of " << std::fixed << maxmem
             << " MB -- skipping" << endl;
    }

    return l_Undef;
}

lbool SLS::run_genetic()
{
    GeneticSAT genetic(solver);
    double mem_needed_mb = (double)approx_mem_needed()/(1000.0*1000.0);
    double maxmem = solver->conf.sls_memoutMB*solver->conf.var_and_mem_out_mult;
    if (mem_needed_mb < maxmem) {
        lbool ret = genetic.main();
        return ret;
    }

    if (solver->conf.verbosity) {
        cout << "c [sls] would need "
             << std::setprecision(2) << std::fixed << mem_needed_mb
             << " MB but that's over limit of " << std::fixed << maxmem
             << " MB -- skipping" << endl;
    }

    return l_Undef;
}

#ifdef USE_YALSAT
lbool SLS::run_yalsat()
{
    Yalsat yalsat(solver);
    double mem_needed_mb = (double)approx_mem_needed()/(1000.0*1000.0);
    double maxmem = solver->conf.sls_memoutMB*solver->conf.var_and_mem_out_mult;
    if (mem_needed_mb < maxmem) {
        lbool ret = yalsat.main();
        return ret;
    }

    if (solver->conf.verbosity) {
        cout << "c [sls] would need "
        << std::setprecision(2) << std::fixed << mem_needed_mb
        << " MB but that's over limit of " << std::fixed << maxmem
        << " MB -- skipping" << endl;
    }

    return l_Undef;
}
#endif

lbool SLS::run_ccnr(const uint32_t num_sls_called)
{
    CMS_ccnr ccnr(solver);
    double mem_needed_mb = (double)approx_mem_needed()/(1000.0*1000.0);
    double maxmem = solver->conf.sls_memoutMB*solver->conf.var_and_mem_out_mult;
    if (mem_needed_mb < maxmem) {
        lbool ret = ccnr.main(num_sls_called);
        return ret;
    }

    if (solver->conf.verbosity) {
        cout << "c [sls] would need "
        << std::setprecision(2) << std::fixed << mem_needed_mb
        << " MB but that's over limit of " << std::fixed << maxmem
        << " MB -- skipping" << endl;
    }

    return l_Undef;
}

uint64_t SLS::approx_mem_needed()
{
    uint32_t numvars = solver->nVars();
    uint32_t numclauses = solver->longIrredCls.size() + solver->binTri.irredBins;
    uint64_t numliterals = solver->litStats.irredLits + solver->binTri.irredBins*2;
    uint64_t needed = 0;

    //LIT storage (all clause data)
    needed += (solver->litStats.irredLits+solver->binTri.irredBins*2)*sizeof(Lit);

    //This is just an estimation of yalsat's memory needs.

    //clause
    needed += sizeof(Lit *) * numclauses;
    //clsize
    needed += sizeof(uint32_t) * numclauses;

    //false_cls
    needed += sizeof(uint32_t) * numclauses;
    //map_cl_to_false_cls
    needed += sizeof(uint32_t) * numclauses;
    //numtruelit
    needed += sizeof(uint32_t) * numclauses;

    //occurrence
    needed += sizeof(uint32_t *) * (2 * numvars);
    //numoccurrence
    needed += sizeof(uint32_t) * (2 * numvars);
    //assigns
    needed += sizeof(lbool) * numvars;
    //breakcount
    needed += sizeof(uint32_t) * numvars;
    //makecount
    needed += sizeof(uint32_t) * numvars;

    //occur_list_alloc
    needed += sizeof(uint32_t) * numliterals;


    return needed;
}
