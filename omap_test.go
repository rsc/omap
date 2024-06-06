// Copyright 2024 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build go1.23

package omap

import (
	"bytes"
	"cmp"
	"fmt"
	"iter"
	"math/rand/v2"
	"slices"
	"testing"
)

type Interface[K, V any] interface {
	All() iter.Seq2[K, V]
	Delete(key K)
	DeleteRange(lo, hi K)
	Get(key K) (V, bool)
	Scan(lo, hi K) iter.Seq2[K, V]
	Set(key K, val V)
	root() **node[K, V]
}

func permute(m Interface[int, int], n int) (perm, slice []int) {
	perm = rand.Perm(n)
	slice = make([]int, 2*n+1)
	for i, x := range perm {
		m.Set(2*x+1, i+1)
		slice[2*x+1] = i + 1
	}
	// Overwrite-Set half the entries.
	for i, x := range perm[:len(perm)/2] {
		m.Set(2*x+1, i+100)
		slice[2*x+1] = i + 100
	}
	return perm, slice
}

func dump(m Interface[int, int]) string {
	var buf bytes.Buffer
	var walk func(*node[int, int])
	walk = func(x *node[int, int]) {
		if x == nil {
			fmt.Fprintf(&buf, "nil")
			return
		}
		fmt.Fprintf(&buf, "(%d ", x.key)
		walk(x.left)
		fmt.Fprintf(&buf, " ")
		walk(x.right)
		fmt.Fprintf(&buf, ")")
	}
	walk(*m.root())
	return buf.String()
}

func test(t *testing.T, f func(*testing.T, func() Interface[int, int])) {
	t.Run("Map", func(t *testing.T) {
		f(t, func() Interface[int, int] { return new(Map[int, int]) })
	})
	t.Run("MapFunc", func(t *testing.T) {
		f(t, func() Interface[int, int] { return NewMapFunc[int, int](cmp.Compare) })
	})
}

func TestGet(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		for N := range 11 {
			m := newMap()
			_, slice := permute(m, N)
			for k, want := range slice {
				v, ok := m.Get(k)
				if v != want || ok != (want > 0) {
					t.Fatalf("Get(%d) = %d, %v, want %d, %v\nM: %v", k, v, ok, want, want > 0, dump(m))
				}
			}
		}
	})
}

func TestAll(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		for N := range 11 {
			m := newMap()
			_, slice := permute(m, N)
			var have []int
			for k, v := range m.All() {
				if v != slice[k] {
					t.Errorf("All() returned %d, %d want %d, %d", k, v, k, slice[k])
				}
				have = append(have, k)
				if len(have) > N+5 { // too many; looping?
					break
				}
			}
			var want []int
			for k, v := range slice {
				if v != 0 {
					want = append(want, k)
				}
			}
			if !slices.Equal(have, want) {
				t.Errorf("All() = %v, want %v", have, want)
			}
		}
	})
}

func TestScan(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		for N := range 11 {
			m := newMap()
			_, slice := permute(m, N)
			for hi := range slice {
				for lo := range hi + 1 {
					var have []int
					for k, v := range m.Scan(lo, hi) {
						if v != slice[k] {
							t.Errorf("All() returned %d, %d want %d, %d", k, v, k, slice[k])
						}
						have = append(have, k)
						if len(have) > N+5 { // too many; looping?
							break
						}
					}
					var want []int
					for k, v := range slice {
						if v != 0 && lo <= k && k <= hi {
							want = append(want, k)
						}
					}
					if !slices.Equal(have, want) {
						t.Errorf("All() = %v, want %v", have, want)
					}
				}
			}
		}
	})
}

func TestDelete(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		for N := range 11 {
			m := newMap()
			_, slice := permute(m, N)
			for _, x := range rand.Perm(len(slice)) {
				m.Delete(x)
				slice[x] = 0
				var have []int
				for k, _ := range m.All() {
					have = append(have, k)
				}
				var want []int
				for x, v := range slice {
					if v != 0 {
						want = append(want, x)
					}
				}
				slices.Sort(want)
				if !slices.Equal(have, want) {
					t.Errorf("after Delete(%v), All() = %v, want %v", x, have, want)
				}
			}
		}
	})
}

func TestDeleteRange(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		for N := range 11 {
			for hi := range 2*N + 1 {
				for lo := range hi + 1 {
					m := newMap()
					_, slice := permute(m, N)
					if lo < hi {
						m.DeleteRange(hi, lo) // want no-op
					}
					m.DeleteRange(lo, hi)
					var have []int
					for k, _ := range m.All() {
						have = append(have, k)
					}
					var want []int
					for k, v := range slice {
						if v != 0 && (k < lo || hi < k) {
							want = append(want, k)
						}
					}
					if !slices.Equal(have, want) {
						t.Errorf("after DeleteRange(%d, %d), All() = %v, want %v", lo, hi, have, want)
					}
				}
			}
		}
	})
}

func TestScanDelete(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		for _, mode := range []string{"prev", "current", "next"} {
			for N := range 8 {
				for target := 1; target <= 2*N-1; target += 2 {
					m := newMap()
					_, slice := permute(m, N)
					var have []int
					var deleted int
					for k, _ := range m.All() {
						if k == target {
							switch mode {
							case "prev":
								deleted = k - 2
							case "current":
								deleted = k
							case "next":
								deleted = k + 2
								if k+2 < len(slice) {
									slice[k+2] = 0
								}
							}
							m.Delete(deleted)
						}
						have = append(have, k)
					}
					var want []int
					for k, v := range slice {
						if v != 0 {
							want = append(want, k)
						}
					}
					if !slices.Equal(have, want) {
						t.Errorf("All() with Delete(%d) at %d = %v, want %v", deleted, target, have, want)
					}
				}
			}
		}
	})
}

func TestScanDeleteRange(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		for _, mode := range []string{"prev", "current", "next"} {
			for N := range 8 {
				for target := 1; target <= 2*N-1; target += 2 {
					m := newMap()
					_, slice := permute(m, N)
					var have []int
					var deleteLo, deleteHi int
					for k, _ := range m.All() {
						if k == target {
							switch mode {
							case "prev":
								deleteLo, deleteHi = k-5, k-1
							case "current":
								deleteLo, deleteHi = k-2, k+2
								if k+2 < len(slice) {
									slice[k+2] = 0
								}
							case "next":
								deleteLo, deleteHi = k+1, k+5
								if k+2 < len(slice) {
									slice[k+2] = 0
								}
								if k+4 < len(slice) {
									slice[k+4] = 0
								}
							}
							m.DeleteRange(deleteLo, deleteHi)
						}
						have = append(have, k)
					}
					var want []int
					for k, v := range slice {
						if v != 0 {
							want = append(want, k)
						}
					}
					if !slices.Equal(have, want) {
						t.Errorf("All() with DeleteRange(%d, %d) at %d = %v, want %v", deleteLo, deleteHi, target, have, want)
					}
				}
			}
		}
	})
}
