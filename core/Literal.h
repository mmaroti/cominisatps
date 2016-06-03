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

class Literal {
	int x;

	constexpr Literal(int x) :
			x(x) {
	}

public:
	constexpr Literal() :
			x(-2) {
	}

	constexpr Literal(Var var, bool sign) :
			x(var + var + (unsigned int) sign) {
	}

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
		return Literal(x ^ 1);
	}

	Literal operator ^(bool b) {
		return Literal(x ^ (unsigned int) b);
	}

	bool sign() const {
		return x & 1;
	}

	int var() const {
		return x >> 1;
	}

	int toInt() const {
		return x;
	}
};

constexpr static Literal LIT_UNDEF = Literal();

}

#endif