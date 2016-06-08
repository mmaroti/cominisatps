/****************************************************************************************[Solver.h]
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

#ifndef Minisat_Solver_h
#define Minisat_Solver_h

#define GLUCOSE23
//#define EXTRA_VAR_ACT_BUMP

#ifdef GLUCOSE23
  #define EXTRA_VAR_ACT_BUMP
#endif

#include "mtl/Vec.h"
#include "mtl/Heap.h"
#include "mtl/Alg.h"
#include "mtl/Queue.h"
#include "utils/Options.h"
#include "SolverTypes.h"
#include "Bool.h"
#include "Values.h"


// Don't change the actual numbers.
#define LOCAL 0
#define TIER2 2
#define CORE  3

namespace Minisat {

//=================================================================================================
// Solver -- the main class:

class Solver {
public:

    // Constructor/Destructor:
    //
    Solver();
    virtual ~Solver();

    // Problem specification:
    //
    Var     newVar    (bool polarity = true, bool dvar = true); // Add a new variable with parameters specifying variable mode.

    bool    addClause (const vec<Literal>& ps);                     // Add a clause to the solver. 
    bool    addEmptyClause();                                   // Add the empty clause, making the solver contradictory.
    bool    addClause (Literal p);                                  // Add a unit clause to the solver. 
    bool    addClause (Literal p, Literal q);                           // Add a binary clause to the solver. 
    bool    addClause (Literal p, Literal q, Literal r);                    // Add a ternary clause to the solver. 
    bool    addClause_(      vec<Literal>& ps);                     // Add a clause to the solver without making superflous internal copy. Will
                                                                // change the passed vector 'ps'.

    // Solving:
    //
    bool    simplify     ();                        // Removes already satisfied clauses.
    Bool   solveLimited ();                        // Search for a model (With resource constraints).
    bool    solve        ();                        // Search without assumptions.
    bool    okay         () const;                  // FALSE means solver is in a conflicting state

    // Variable mode:
    // 
    void    setDecisionVar (Var v, bool b); // Declare if a variable should be eligible for selection in the decision heuristic.

    // Read state:
    //
    Bool   modelValue (Var x) const;       // The value of a variable in the last model. The last call to solve must have been satisfiable.
    Bool   modelValue (Literal p) const;       // The value of a literal in the last model. The last call to solve must have been satisfiable.
    int     nAssigns   ()      const;       // The current number of assigned literals.
    int     nClauses   ()      const;       // The current number of original clauses.
    int     nLearnts   ()      const;       // The current number of learnt clauses.
    int     nVars      ()      const;       // The current number of variables.
    int     nFreeVars  ()      const;

    // Memory managment:
    //
    virtual void garbageCollect();
    void    checkGarbage(double gf);
    void    checkGarbage();

    // Extra results: (read-only member variable)
    //
    vec<Bool> model;             // If problem is satisfiable, this vector contains the model (if any).
    vec<Literal>   conflict;          // If problem is unsatisfiable (possibly under assumptions),
                                  // this vector represent the final conflict clause expressed in the assumptions.

    // Mode of operation:
    //
    int       verbosity;
    double    var_decay_no_r;
    double    var_decay_glue_r;
    double    clause_decay;
    double    random_seed;
    bool      glucose_restart;
    int       ccmin_mode;         // Controls conflict clause minimization (0=none, 1=basic, 2=deep).
    int       phase_saving;       // Controls the level of phase saving (0=none, 1=limited, 2=full).
    bool      rnd_init_act;       // Initialize variable activities with a small random value.
    double    garbage_frac;       // The fraction of wasted memory allowed before a garbage collection is triggered.

    // Statistics: (read-only member variable)
    //
    uint64_t solves, starts, decisions, rnd_decisions, propagations, conflicts, conflicts_glue;
    uint64_t clauses_literals, learnts_literals, max_literals, tot_literals;

protected:

    // Solver state:
    //
    bool                ok;               // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    vec<CRef>           clauses;          // List of problem clauses.
    vec<CRef>           learnts_core,     // List of learnt clauses.
                        learnts_tier2,
                        learnts_local;
    bool                tier2_learnts_dirty,
                        local_learnts_dirty;
    double              cla_inc;          // Amount to bump next clause with.
    vec<double>         activity_no_r,    // A heuristic measurement of the activity of a variable.
                        activity_glue_r;
    double              var_inc_no_r,     // Amount to bump next variable with.
                        var_inc_glue_r;
    OccLists            watches_bin,      // Watches for binary clauses only.
                        watches;          // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    Values			    values;			  // the current assignments
    vec<Literal>        trail;            // Assignment stack; stores all assignments made in the order they were made.
    vec<int>            trail_lim;        // Separator indices for different decision levels in 'trail'.
    int                 qhead;            // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
    int                 simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
    int64_t             simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.
    Heap<VarOrderLt>    order_heap_no_r,  // A priority queue of variables ordered with respect to the variable activity.
                        order_heap_glue_r;
    bool                remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.

    int                 core_lbd_cut;
    float               global_lbd_sum;
    Queue<int>          lbd_queue;        // For computing moving averages of recent LBD values.

    uint64_t            next_T2_reduce,
                        next_L_reduce;

    ClauseAllocator     ca;

    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, exept 'seen' wich is used in several places.
    //
    vec<char>           seen;
    vec<Literal>            analyze_stack;
    vec<Literal>            analyze_toclear;
    vec<Literal>            add_tmp;

    vec<uint64_t>       seen2;    // Mostly for efficient LBD computation. 'seen2[i]' will indicate if decision level or variable 'i' has been seen.
    uint64_t            counter;  // Simple counter for marking purpose with 'seen2'.

    // Main internal methods:
    //
    void     insertVarOrder   (Var x);                                                 // Insert a variable in the decision order priority queue.
    Literal      pickBranchLit    ();                                                      // Return the next decision variable.
    void     newDecisionLevel ();                                                      // Begins a new decision level.
    void     uncheckedEnqueue (Literal p, CRef from = CRef_Undef);                         // Enqueue a literal. Assumes value of literal is undefined.
    CRef     propagate        ();                                                      // Perform unit propagation. Returns possibly conflicting clause.
    void     cancelUntil      (int level);                                             // Backtrack until a certain level.
    void     analyze          (CRef confl, vec<Literal>& out_learnt, int& out_btlevel, int& out_lbd);    // (bt = backtrack)
    bool     litRedundant     (Literal p, uint32_t abstract_levels);                       // (helper method for 'analyze()')
    Bool    search           (int& nof_conflicts);                                    // Search for a given number of conflicts.
    Bool    solve_           ();                                                      // Main solve method (assumptions given in 'assumptions').
    void     reduceDB         ();                                                      // Reduce the set of learnt clauses.
    void     reduceDB_Tier2   ();
    void     removeSatisfied  (vec<CRef>& cs);                                         // Shrink 'cs' to contain only non-satisfied clauses.
    void     rebuildOrderHeap ();
    bool     binResMinimize   (vec<Literal>& out_learnt);                                  // Further learnt clause minimization by binary resolution.
    void     cleanLearnts     (vec<CRef>& learnts, unsigned valid_mark);

    // Maintaining Variable/Clause activity:
    //
    void     varDecayActivity ();                      // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
    void     varBumpActivity  (Var v);                 // Increase a variable with the current 'bump' value.
    void     claDecayActivity ();                      // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.
    void     claBumpActivity  (Clause& c);             // Increase a clause with the current 'bump' value.

    // Operations on clauses:
    //
    void     attachClause     (CRef cr);               // Attach a clause to watcher lists.
    void     detachClause     (CRef cr, bool strict = false); // Detach a clause to watcher lists.
    void     removeClause     (CRef cr);               // Detach and free a clause.
    bool     locked           (const Clause& c) const; // Returns TRUE if a clause is a reason for some implication in the current state.
    bool     satisfied        (const Clause& c) const; // Returns TRUE if a clause is satisfied in the current state.

    void     relocAll         (ClauseAllocator& to);

    // Misc:
    //
    int      decisionLevel    ()      const; // Gives the current decisionlevel.
    uint32_t abstractLevel    (Literal p) const; // Used to represent an abstraction of sets of decision levels.

    template<class V> int computeLBD(const V& c) {
        int lbd = 0;

        counter++;
        for (int i = 0; i < c.size(); i++){
            int l = values.getLevel(c[i]);
            if (l != 0 && seen2[l] != counter){
                seen2[l] = counter;
                lbd++; } }

        return lbd;
    }

    // Static helpers:
    //

    // Returns a random float 0 <= x < 1. Seed must never be 0.
    static inline double drand(double& seed) {
        seed *= 1389796;
        int q = (int)(seed / 2147483647);
        seed -= (double)q * 2147483647;
        return seed / 2147483647; }

    // Returns a random integer 0 <= x < size. Seed must never be 0.
    static inline int irand(double& seed, int size) {
        return (int)(drand(seed) * size); }
};


//=================================================================================================
// Implementation of inline methods:

inline void Solver::insertVarOrder(Var x) {
    Heap<VarOrderLt>& order_heap = glucose_restart ? order_heap_glue_r : order_heap_no_r;
    if (!order_heap.inHeap(x) && values.getDecision(x)) order_heap.insert(x); }

inline void Solver::varDecayActivity() {
    var_inc_glue_r *= (1 / var_decay_glue_r);
    var_inc_no_r   *= (1 / var_decay_no_r); }

inline void Solver::varBumpActivity(Var v) {
    if ( (activity_no_r[v] += var_inc_no_r) > 1e100 ) {
        // Rescale:
        for (int i = 0; i < nVars(); i++)
            activity_no_r[i] *= 1e-100;
        var_inc_no_r *= 1e-100; }
    if ( (activity_glue_r[v] += var_inc_glue_r) > 1e100 ) {
        // Rescale:
        for (int i = 0; i < nVars(); i++)
            activity_glue_r[i] *= 1e-100;
        var_inc_glue_r *= 1e-100; }

    // Update order_heap with respect to new activity:
    if (order_heap_no_r  .inHeap(v)) order_heap_no_r  .decrease(v);
    if (order_heap_glue_r.inHeap(v)) order_heap_glue_r.decrease(v); }

inline void Solver::claDecayActivity() { cla_inc *= (1 / clause_decay); }
inline void Solver::claBumpActivity (Clause& c) {
        if ( (c.activity() += cla_inc) > 1e20 ) {
            // Rescale:
            for (int i = 0; i < learnts_local.size(); i++)
                ca[learnts_local[i]].activity() *= 1e-20;
            cla_inc *= 1e-20; } }

inline void Solver::checkGarbage(void){ return checkGarbage(garbage_frac); }
inline void Solver::checkGarbage(double gf){
    if (ca.wasted() > ca.size() * gf)
        garbageCollect(); }

inline bool     Solver::addClause       (const vec<Literal>& ps)    { ps.copyTo(add_tmp); return addClause_(add_tmp); }
inline bool     Solver::addEmptyClause  ()                      { add_tmp.clear(); return addClause_(add_tmp); }
inline bool     Solver::addClause       (Literal p)                 { add_tmp.clear(); add_tmp.push(p); return addClause_(add_tmp); }
inline bool     Solver::addClause       (Literal p, Literal q)          { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); return addClause_(add_tmp); }
inline bool     Solver::addClause       (Literal p, Literal q, Literal r)   { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); add_tmp.push(r); return addClause_(add_tmp); }
inline bool     Solver::locked          (const Clause& c) const {
    int i = c.size() != 2 ? 0 : (values.isTrue(c[0]) ? 0 : 1);
    return values.isTrue(c[i]) && values.getReason(c[i]) != CRef_Undef && ca.lea(values.getReason(c[i])) == &c;
}
inline void     Solver::newDecisionLevel()                      { trail_lim.push(trail.size()); }

inline int      Solver::decisionLevel ()      const   { return trail_lim.size(); }
inline uint32_t Solver::abstractLevel (Literal p) const   { return 1 << (values.getLevel(p) & 31); }
inline Bool    Solver::modelValue    (Var x) const   { return model[x]; }
inline Bool    Solver::modelValue    (Literal p) const   { return model[p.var()] ^ p.sign(); }
inline int      Solver::nAssigns      ()      const   { return trail.size(); }
inline int      Solver::nClauses      ()      const   { return clauses.size(); }
inline int      Solver::nLearnts      ()      const   { return learnts_core.size() + learnts_tier2.size() + learnts_local.size(); }
inline int      Solver::nVars         ()      const   { return values.getVarCount(); }
inline int      Solver::nFreeVars     ()      const   { return values.getDecisionVars() - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]); }

inline bool     Solver::solve         () { return solve_().isTrue(); }
inline Bool    Solver::solveLimited  () { return solve_(); }
inline bool     Solver::okay          ()      const   { return ok; }

//=================================================================================================
}

#endif
