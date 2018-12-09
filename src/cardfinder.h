/******************************************
Copyright (c) 2018, Mate Soos

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

#ifndef _CARDFINDER_H_
#define _CARDFINDER_H_

#include <vector>
#include <set>
#include <iostream>
#include <algorithm>
#include <set>
#include <limits>
#include "xor.h"
#include "cset.h"
#include "watcharray.h"

using std::vector;
using std::set;

namespace CMSat {

class Solver;

class CardFinder
{

public:
    CardFinder(Solver* solver);
    void find_cards();
    const vector<vector<Lit>>& get_cards() const;

private:
    bool find_connector(Lit lit1, Lit lit2) const;
    Solver* solver;

    vector<vector<Lit>> cards;
    uint64_t total_sizes = 0;
};

inline const vector<vector<Lit>>& CardFinder::get_cards() const
{
    return cards;
}

} //end namespace

#endif //_CARDFINDER_H_
