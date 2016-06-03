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

#ifndef MINISAT_LITERAL_H
#define MINISAT_LITERAL_H

namespace Minisat {

typedef int Var;
constexpr static Var VAR_UNDEF = { -1 };

struct Literal {
	int x;

	// Use this as a constructor:
	friend Literal mkLit(Var var, bool sign = false);

	bool operator ==(Literal p) const {
		return x == p.x;
	}

	bool operator !=(Literal p) const {
		return x != p.x;
	}

	bool operator <(Literal p) const {
		return x < p.x;
	}

	Literal operator ~() const {
		Literal q;
		q.x = x ^ 1;
		return q;
	}

	Literal operator ^(bool b) {
		Literal q;
		q.x = x ^ (unsigned int) b;
		return q;
	}

	bool sign() const {
		return x & 1;
	}

	int var() const {
		return x >> 1;
	}
};

inline Literal mkLit(Var var, bool sign) {
	Literal p;
	p.x = var + var + (int) sign;
	return p;
}

inline int toInt(Literal p) {
	return p.x;
}

constexpr static Literal LIT_UNDEF = { -2 };

}

#endif
