// Copyright 2024 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package omap

import (
	"math/rand/v2"
	"testing"
)

var getMap, getMapSeq *Map[int, int]

func benchMaps(b *testing.B, bench func(b *testing.B, newMap func() Mapper[int, int])) {
	for _, m := range maps {
		b.Run(m.name, func(b *testing.B) { bench(b, m.new) })
	}
}

func BenchmarkGetRandRand(b *testing.B) {
	benchMaps(b, func(b *testing.B, newMap func() Mapper[int, int]) {
		const N = 100000
		m := newMap()
		rand := rand.New(rand.NewPCG(1, 1))
		perm := rand.Perm(N)
		for _, v := range rand.Perm(N) {
			m.Set(v, v)
		}
		//b.Logf("depth=%v", m.Depth())
		perm = rand.Perm(N)
		b.ResetTimer()
		n := 0
		for range b.N {
			m.Get(perm[n])
			n++
			if n == N {
				n = 0
			}
		}
	})
}

func BenchmarkGetSeqRand(b *testing.B) {
	benchMaps(b, func(b *testing.B, newMap func() Mapper[int, int]) {
		const N = 100000
		rand := rand.New(rand.NewPCG(1, 1))
		m := newMap()
		for v := range N {
			m.Set(v, v)
		}
		//b.Logf("depth=%v", m.Depth())
		perm := rand.Perm(N)
		b.ResetTimer()
		n := 0
		for range b.N {
			m.Get(perm[n])
			n++
			if n == N {
				n = 0
			}
		}
	})
}

func BenchmarkSetDelete(b *testing.B) {
	benchMaps(b, func(b *testing.B, newMap func() Mapper[int, int]) {
		const N = 100000
		perm := rand.Perm(N)
		perm2 := rand.Perm(N)
		m := newMap()
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
	})
}
