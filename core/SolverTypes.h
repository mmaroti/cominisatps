/***********************************************************************************[SolverTypes.h]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
           Copyright (c) 2007-2010, Niklas Sorensson

Chanseok Oh's MiniSat Patch Series -- Copyright (c) 2015, Chanseok Oh

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/


#ifndef Minisat_SolverTypes_h
#define Minisat_SolverTypes_h

#include <assert.h>

#include "mtl/Alg.h"
#include "mtl/Vec.h"
#include "mtl/Map.h"
#include "mtl/Alloc.h"
#include "core/Literal.h"

namespace Minisat {

//=================================================================================================
// Clause -- a simple class for representing a clause:

class Clause;
typedef RegionAllocator<uint32_t>::Ref CRef;

class Clause {
    struct {
        unsigned learnt    : 1;
        unsigned mark      : 2;
        unsigned reloced   : 1;
        unsigned removable : 1;
        unsigned lbd       : 27;
        uint32_t size;
    } header;
    union { Literal lit; float act; uint32_t touched; CRef rel; } data[0];

    friend class ClauseAllocator;

    // NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
    template<class V>
    Clause(const V& ps, bool learnt) {
        header.size      = ps.size();
        header.learnt    = learnt;
        header.mark      = 0;
        header.reloced   = 0;
        header.removable = 1;
        header.lbd       = 0;

        for (int i = 0; i < ps.size(); i++) 
            data[i].lit = ps[i];

        if (header.learnt){
                data[header.size].act = 0; 
                data[header.size+1].touched = 0;
        }
    }

public:

    int          size        ()      const   { return header.size; }
    void         shrink      (int i)         { assert(i <= size()); if (header.learnt) data[header.size-i] = data[header.size]; header.size -= i; }
    void         pop         ()              { shrink(1); }
    bool         learnt      ()      const   { return header.learnt; }
    uint32_t     mark        ()      const   { return header.mark; }
    void         mark        (uint32_t m)    { header.mark = m; }
    const Literal&   last        ()      const   { return data[header.size-1].lit; }

    bool         reloced     ()      const   { return header.reloced; }
    CRef         relocation  ()      const   { return data[0].rel; }
    void         relocate    (CRef c)        { header.reloced = 1; data[0].rel = c; }

    int          lbd         ()      const   { return header.lbd; }
    void         set_lbd     (int lbd)       { header.lbd = lbd; }
    bool         removable   ()      const   { return header.removable; }
    void         removable   (bool b)        { header.removable = b; }

    // NOTE: somewhat unsafe to change the clause in-place! Must manually call 'calcAbstraction' afterwards for
    //       subsumption operations to behave correctly.
    Literal&         operator [] (int i)         { return data[i].lit; }
    Literal          operator [] (int i) const   { return data[i].lit; }
    operator const Literal* (void) const         { return (Literal*)data; }

    uint32_t&    touched     ()              { assert(header.learnt); return data[header.size+1].touched; }
    float&       activity    ()              { assert(header.learnt); return data[header.size].act; }
};


//=================================================================================================
// ClauseAllocator -- a simple class for allocating memory for clauses:


const CRef CRef_Undef = RegionAllocator<uint32_t>::Ref_Undef;
class ClauseAllocator : public RegionAllocator<uint32_t>
{
    static int clauseWord32Size(int size, int extras){
        return (sizeof(Clause) + (sizeof(Literal) * (size + extras))) / sizeof(uint32_t); }
 public:
    ClauseAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap) {}
    ClauseAllocator() {}

    void moveTo(ClauseAllocator& to){
        RegionAllocator<uint32_t>::moveTo(to); }

    template<class Lits>
    CRef alloc(const Lits& ps, bool learnt = false)
    {
        assert(sizeof(Literal)      == sizeof(uint32_t));
        assert(sizeof(float)    == sizeof(uint32_t));
        int extras = learnt ? 2 : 0;

        CRef cid = RegionAllocator<uint32_t>::alloc(clauseWord32Size(ps.size(), extras));
        new (lea(cid)) Clause(ps, learnt);

        return cid;
    }

    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    Clause&       operator[](Ref r)       { return (Clause&)RegionAllocator<uint32_t>::operator[](r); }
    const Clause& operator[](Ref r) const { return (Clause&)RegionAllocator<uint32_t>::operator[](r); }
    Clause*       lea       (Ref r)       { return (Clause*)RegionAllocator<uint32_t>::lea(r); }
    const Clause* lea       (Ref r) const { return (Clause*)RegionAllocator<uint32_t>::lea(r); }
    Ref           ael       (const Clause* t){ return RegionAllocator<uint32_t>::ael((uint32_t*)t); }

    void free(CRef cid)
    {
        Clause& c = operator[](cid);
        int extras = c.learnt() ? 2 : 0;
        RegionAllocator<uint32_t>::free(clauseWord32Size(c.size(), extras));
    }

    void reloc(CRef& cr, ClauseAllocator& to)
    {
        Clause& c = operator[](cr);
        
        if (c.reloced()) { cr = c.relocation(); return; }
        
        cr = to.alloc(c, c.learnt());
        c.relocate(cr);
        
        // Copy extra data-fields: 
        // (This could be cleaned-up. Generalize Clause-constructor to be applicable here instead?)
        to[cr].mark(c.mark());
        if (to[cr].learnt()){
            to[cr].touched() = c.touched();
            to[cr].activity() = c.activity();
            to[cr].set_lbd(c.lbd());
            to[cr].removable(c.removable());
        }
    }
};

//=================================================================================================

// Helper structures:
//
struct VarData { CRef reason; int level; };
static inline VarData mkVarData(CRef cr, int l){ VarData d = {cr, l}; return d; }

struct Watcher {
    CRef cref;
    Literal  blocker;
    Watcher(CRef cr, Literal p) : cref(cr), blocker(p) {}
    bool operator==(const Watcher& w) const { return cref == w.cref; }
    bool operator!=(const Watcher& w) const { return cref != w.cref; }
};

struct VarOrderLt {
    const vec<double>&  activity;
    bool operator () (Var x, Var y) const { return activity[x] > activity[y]; }
    VarOrderLt(const vec<double>&  act) : activity(act) { }
};

//=================================================================================================
// OccLists -- a class for maintaining occurence lists with lazy deletion:

class OccLists {
	vec<vec<Watcher>> occs;
	vec<char> dirty;
	vec<Literal> dirties;
	const ClauseAllocator& ca;

	bool isDeleted(const Watcher& w) {
		return ca[w.cref].mark() == 1;
	}

public:
	OccLists(const ClauseAllocator& ca) :
			ca(ca) {
	}

	void init(Literal lit) {
		occs.growTo(lit.toInt() + 1);
		dirty.growTo(lit.toInt() + 1, 0);
	}

	vec<Watcher>& operator[](Literal lit) {
		return occs[lit.toInt()];
	}

	void cleanAll() {
		for (int i = 0; i < dirties.size(); i++)
			clean(dirties[i]);
		dirties.clear();
	}

	void clean(Literal lit) {
		vec<Watcher>& vec = occs[lit.toInt()];
		int i, j;
		for (i = j = 0; i < vec.size(); i++)
			if (!isDeleted(vec[i]))
				vec[j++] = vec[i];
		vec.shrink(i - j);
		dirty[lit.toInt()] = 0;
	}

	void smudge(Literal lit) {
		if (dirty[lit.toInt()] == 0) {
			dirty[lit.toInt()] = 1;
			dirties.push(lit);
		}
	}
};

}

#endif
