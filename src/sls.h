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

#ifndef SLS_H_
#define SLS_H_

#include "solvertypes.h"

namespace CMSat {

class Solver;

class SLS {
public:
    SLS(Solver* solver);
    ~SLS();
    lbool run(const uint32_t num_sls_called);

private:
    Solver* solver;

    lbool run_walksat();
    lbool run_walksatlm();
    lbool run_walksatmvt();
    lbool run_oneplusone();
    lbool run_oneplusonefea();
    lbool run_oneplusonefeaup();
    lbool run_oneplusoneyasa();
    lbool run_genetic();

    #ifdef USE_YALSAT
    lbool run_yalsat();
    #endif
    lbool run_ccnr(const uint32_t num_sls_called);
    uint64_t approx_mem_needed();
};

} //end namespace CMSat

#endif //SLS_H_
