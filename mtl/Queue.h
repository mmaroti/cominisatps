/*
 * Copyright (c) 2006-2010, Niklas Sorensson
 * Copyright (c) 2015, Chanseok Oh
 */

#ifndef Minisat_Queue_h
#define Minisat_Queue_h

#include "mtl/Vec.h"
#include <cassert>

namespace Minisat {
template<typename T>
class Queue {
	int max_sz, q_sz;
	int ptr;
	int64_t sum;
	vec<T> q;

public:
	Queue(int sz) :
			max_sz(sz), q_sz(0), ptr(0), sum(0) {
		assert(sz > 0);
		q.growTo(sz);
	}

	inline bool full() const {
		return q_sz == max_sz;
	}

	inline T avg() const {
		assert(full());
		return sum / max_sz;
	}

	inline void clear() {
		sum = 0;
		q_sz = 0;
		ptr = 0;
	}

	void push(T e) {
		if (q_sz < max_sz)
			q_sz++;
		else
			sum -= q[ptr];

		sum += e;
		q[ptr++] = e;
		if (ptr == max_sz)
			ptr = 0;
	}
};

}

#endif
