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

#ifndef MINISAT_BOOL_H
#define MINISAT_BOOL_H

namespace Minisat {

class Bool {
	int8_t val;

public:
	constexpr explicit Bool(int8_t x) :
			val(x) {
	}

	constexpr Bool() :
			val(0) {
	}

	constexpr explicit Bool(bool x) :
			val(x ? (int8_t) 1 : (int8_t) -1) {
	}

	Bool operator ^(bool b) const {
		return Bool(b ? (int8_t) -val : val);
	}

	Bool operator &&(Bool b) const {
		return Bool(val <= b.val ? val : b.val);
	}

	Bool operator ||(Bool b) const {
		return Bool(val >= b.val ? val : b.val);
	}

	// disable explicit equality
	bool operator ==(Bool b) const = delete;

	bool operator !=(Bool b) const = delete;

	bool isTrue() const {
		return val > 0;
	}

	bool isFalse() const {
		return val < 0;
	}

	bool isUndef() const {
		return val == 0;
	}
};

constexpr static Bool BOOL_TRUE = Bool((int8_t) 1);
constexpr static Bool BOOL_FALSE = Bool((int8_t) -1);
constexpr static Bool BOOL_UNDEF = Bool((int8_t) 0);

}

#endif
