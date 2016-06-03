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
#include "mtl/Vec.h"

namespace Minisat {

class Values {
	vec<Bool> values;

public:
	void addVariable() {
		values.push(BOOL_UNDEF);
	}

	void setUndef(Var v) {
		values[v] = BOOL_UNDEF;
	}

	void setFalse(Literal lit) {
		values[lit.var()] = lit.sign() ? BOOL_FALSE : BOOL_TRUE;
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
};

}

#endif
