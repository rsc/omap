// Copyright 2024 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package omap

import (
	"math/rand/v2"
	"testing"
)

var getMap, getMapSeq *Map[int, int]

func BenchmarkGet(b *testing.B) {
	const N = 100000
	if getMap == nil {
		m := new(Map[int, int])
		rand := rand.New(rand.NewPCG(1,1))
		for _, v := range rand.Perm(N) {
			m.Set(v, v)
		}
		getMap = m
		b.ResetTimer()
	}
	n := 0
	for range b.N {
		getMap.Get(n)
		n++
		if n == N {
			n = 0
		}
	}
}

func BenchmarkGetSeq(b *testing.B) {
	const N = 100000
	if getMapSeq == nil {
		m := new(Map[int, int])
		for i := range N {
			m.Set(i, i)
		}
		getMapSeq = m
		b.ResetTimer()
	}
	n := 0
	for range b.N {
		getMapSeq.Get(n)
		n++
		if n == N {
			n = 0
		}
	}
}

func BenchmarkSetDelete(b *testing.B) {
	const N = 100000
	perm := rand.Perm(N)
	perm2 := rand.Perm(N)
	m := new(Map[int, int])
	b.ResetTimer()
	n := 0
	for range b.N {
		if n < N {
			m.Set(perm[n], perm[n])
		} else {
			m.Delete(perm2[n-N])
		}
		n++
		if n == 2*N {
			n = 0
		}
	}
}
