/**
 Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
 Copyright (c) 2007-2010, Niklas Sorensson
 Copyright (c) 2015, Chanseok Oh
 Copyright (c) 2016, Miklos Maroti

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
 */

#ifndef MINISAT_VALUES_H
#define MINISAT_VALUES_H

#include "Bool.h"
#include "Literal.h"
#include "SolverTypes.h"
#include "mtl/Vec.h"

namespace Minisat {

class Variables {
	struct Data {
		unsigned polarity :1;	// preferred polarity for next decision
		unsigned decision :1;	// eligible for decision making
		unsigned level :30;		// decision level
		CRef reason;			// clause forcing the decision

		Data(bool p, bool d) :
				polarity(p), decision(d), level(0), reason(CRef_Undef) {
		}
	};

	vec<Bool> values;	// the current assignments of variables
	vec<Data> data;		// auxiliary data for each variable
	int decision_vars;	// number of decision variables

public:
	void addVariable(bool polarity, bool decision) {
		values.push(BOOL_UNDEF);
		data.push(Data(polarity, decision));
		decision_vars += (unsigned) decision;
	}

	Bool getValue(Var v) const {
		return values[v];
	}

	Bool getValue(Literal lit) const {
		return values[lit.var()] ^ lit.sign();
	}

	bool isUndef(Var var) const {
		return getValue(var).isUndef();
	}

	bool isFalse(Literal lit) const {
		return getValue(lit).isFalse();
	}

	bool isTrue(Literal lit) const {
		return getValue(lit).isTrue();
	}

	bool isUndef(Literal lit) const {
		return getValue(lit).isUndef();
	}

	void setUndef(Var v) {
		values[v] = BOOL_UNDEF;
	}

	void setFalse(Literal lit) {
		values[lit.var()] = lit.sign() ? BOOL_FALSE : BOOL_TRUE;
	}

	bool getPolarity(Var var) const {
		return data[var].polarity;
	}

	void setPolarity(Var var, bool polarity) {
		data[var].polarity = (unsigned) polarity;
	}

	bool getDecision(Var var) const {
		return data[var].decision;
	}

	void setDecision(Var var, bool decision) {
		Data &d = data[var];

		decision_vars -= d.decision;
		d.decision = decision;
		decision_vars += d.decision;

		// TODO: update order heap
	}

	int getDecisionVars() const {
		return decision_vars;
	}

	int getVarCount() const {
		return data.size();
	}

	CRef getReason(Literal lit) const {
		return data[lit.var()].reason;
	}

	void setReason(Literal lit, CRef cref) {
		data[lit.var()].reason = cref;
	}

	CRef &refReason(Literal lit) {
		return data[lit.var()].reason;
	}

	int getLevel(Literal lit) const {
		return data[lit.var()].level;
	}

	void setLevel(Literal lit, int level) {
		data[lit.var()].level = level;
	}
};

}

#endif
