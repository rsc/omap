// Copyright 2024 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build go1.23

package omap

import (
	"cmp"
	"fmt"
	"iter"
	"math/rand/v2"
	"slices"
	"sort"
	"testing"
)

type Mapper[K, V any] interface {
	Get(key K) (V, bool)
	All() iter.Seq2[K, V]
	Delete(key K)
	DeleteRange(lo, hi K)
	Scan(lo, hi K) iter.Seq2[K, V]
	Set(key K, val V)
	Dump() string
	Depth() int
}

func permute(m Mapper[int, int], n int) (perm, slice []int) {
	perm = rand.Perm(n)
	slice = make([]int, 2*n+1)
	//println("P")
	for i, x := range perm {
		//println("X", 2*x+1, m.Dump())
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

var maps = []struct {
	name string
	new  func() Mapper[int, int]
}{
	{"Map", func() Mapper[int, int] { return new(Map[int, int]) }},
	{"treapMap", func() Mapper[int, int] { return new(treapMap[int, int]) }},
	{"treapMapFunc", func() Mapper[int, int] {
		m := new(treapMapFunc[int, int])
		m.init(cmp.Compare[int])
		return m
	}},
	{"avlMap", func() Mapper[int, int] { return new(avlMap[int, int]) }},
	{"avlMapFunc", func() Mapper[int, int] {
		m := new(avlMapFunc[int, int])
		m.init(cmp.Compare[int])
		return m
	}},
	{"llrbMap", func() Mapper[int, int] { return new(llrbMap[int, int]) }},
	{"llrbMapFunc", func() Mapper[int, int] {
		m := new(llrbMapFunc[int, int])
		m.init(cmp.Compare[int])
		return m
	}},
}

func test(t *testing.T, f func(*testing.T, func() Mapper[int, int])) {
	for _, m := range maps {
		t.Run(m.name, func(t *testing.T) { f(t, m.new) })
	}
}

func TestGet(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Mapper[int, int]) {
		for N := range 100 {
			m := newMap()
			_, slice := permute(m, N)
			for k, want := range slice {
				v, ok := m.Get(k)
				if v != want || ok != (want > 0) {
					t.Fatalf("Get(%d) = %d, %v, want %d, %v\nM: %v", k, v, ok, want, want > 0, m.Dump())
				}
			}
		}
	})
}

func TestAll(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Mapper[int, int]) {
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
	test(t, func(t *testing.T, newMap func() Mapper[int, int]) {
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
	test(t, func(t *testing.T, newMap func() Mapper[int, int]) {
		for N := range 50 {
			for range 100 {
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
		}
	})
}

func TestDelete2(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Mapper[int, int]) {
		for N := range 5 {
			for perm := range allPerm(N) {
				for dperm := range allPerm(N) {
					m := newMap()
					func() {
						defer func() {
							if e := recover(); e != nil {
								fmt.Println("SET", perm, m.Dump(), "DEL", dperm)
								panic(e)
							}
						}()
						for _, v := range perm {
							m.Set(v, v)
						}
						for _, v := range dperm {
							m.Delete(v)
						}
					}()
				}
			}
		}
	})
}

func TestDelete3(t *testing.T) {
	set := []int{17, 9, 23, 7, 11, 19, 27}
	del := []int{17}
	m := new(llrbMap[int, int])
	for _, v := range set {
		m.Set(v, v)
	}
	for _, v := range del {
		m.Delete(v)
	}
}

func TestDeleteRange(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Mapper[int, int]) {
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
						t.Fatalf("after DeleteRange(%d, %d), All() = %v, want %v", lo, hi, have, want)
					}
				}
			}
		}
	})
}

func TestScanDelete(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Mapper[int, int]) {
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
						var have2 []int
						for k := range m.All() {
							have2 = append(have2, k)
						}
						t.Errorf("All() with Delete(%d) at %d = %v, want %v (after=%v)", deleted, target, have, want, have2)
					}
				}
			}
		}
	})
}

func TestScanDeleteRange(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Mapper[int, int]) {
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

func TestSplit(t *testing.T) {
	split := func(t *testing.T, m Mapper[int, int], target int) (val int, ok bool, more Mapper[int, int]) {
		switch m := m.(type) {
		default:
			t.Fatalf("bad split %T", m)
			panic("unreachable")
		case *Map[int, int]:
			return m.Split(target)
		case *treapMap[int, int]:
			x, after := m.split(target)
			if x != nil {
				val, ok = x.val, true
			}
			more = &treapMap[int, int]{after}
			return val, ok, more
		case *treapMapFunc[int, int]:
			x, after := m.split(target)
			if x != nil {
				val, ok = x.val, true
			}
			more = &treapMapFunc[int, int]{after, m.cmp}
			return val, ok, more
		case *avlMap[int, int]:
			x, after := m.split(target)
			if x != nil {
				val, ok = x.val, true
			}
			more = &avlMap[int, int]{after}
			return val, ok, more
		case *avlMapFunc[int, int]:
			x, after := m.split(target)
			if x != nil {
				val, ok = x.val, true
			}
			more = &avlMapFunc[int, int]{after, m.cmp}
			return val, ok, more
		}
	}

	test(t, func(t *testing.T, newMap func() Mapper[int, int]) {
		for N := range 16 {
			for range 100 {
				for target := 0; target <= 2*N; target++ {
					m := newMap()
					_, slice := permute(m, N)
					orig := getAll(m)
					var want1, want2 []int
					var wantOK bool
					var wantVal int
					for k, v := range slice {
						if v != 0 {
							if k < target {
								want1 = append(want1, k)
							} else if k > target {
								want2 = append(want2, k)
							} else {
								wantOK = true
								wantVal = v
							}
						}
					}
					val, ok, rest := split(t, m, target)
					have1 := getAll(m)
					have2 := getAll(rest)
					if val != wantVal || ok != wantOK || !slices.Equal(have1, want1) || !slices.Equal(have2, want2) {
						t.Fatalf("%v.Split(%v):\nhave m=%v val=%v ok=%v rest=%v\nwant m=%v val=%v ok=%v rest=%v",
							orig, target, have1, val, ok, have2, want1, wantVal, wantOK, want2)
					}
				}
			}
		}
	})
}

func TestJoin(t *testing.T) {
	join := func(t *testing.T, m, more Mapper[int, int]) {
		switch m := m.(type) {
		default:
			t.Fatalf("bad join %T", m)
		case *Map[int, int]:
			m.Join(more.(*Map[int, int]))
		case *treapMap[int, int]:
			more := more.(*treapMap[int, int])
			m.join(nil, more.treap)
			more.root = nil
		case *treapMapFunc[int, int]:
			more := more.(*treapMapFunc[int, int])
			m.join(nil, more.treap)
			more.root = nil
		case *avlMap[int, int]:
			more := more.(*avlMap[int, int])
			m.join(nil, more.avl)
			more.root = nil
		case *avlMapFunc[int, int]:
			more := more.(*avlMapFunc[int, int])
			m.join(nil, more.avl)
			more.root = nil
		}
	}

	test(t, func(t *testing.T, newMap func() Mapper[int, int]) {
		for N := range 16 {
			for range 100 {
				perm := rand.Perm(N)
				target := rand.N(1 + N)

				m1 := newMap()
				m2 := newMap()
				var want1, want2 []int
				for _, v := range perm {
					if v < target {
						m1.Set(v, v)
						want1 = append(want1, v)
					} else {
						m2.Set(v, v)
						want2 = append(want2, v)
					}
				}
				sort.Ints(want1)
				sort.Ints(want2)
				have1 := getAll(m1)
				have2 := getAll(m2)
				if !slices.Equal(have1, want1) || !slices.Equal(have2, want2) {
					t.Fatalf("before join\nperm: %v target: %v\nhave: %v %v\nwant: %v %v", perm, target, have1, have2, want1, want2)
				}
				join(t, m1, m2)
				have1 = getAll(m1)
				have2 = getAll(m2)
				want := slices.Concat(want1, want2)
				if !slices.Equal(have1, want) || !slices.Equal(have2, nil) {
					t.Fatalf("after join\ninputs: %v %v\nhave: %v %v\nwant: %v %v", want1, want2, have1, have2, want, []int{})
				}
			}
		}
	})
}

func getAll(m Mapper[int, int]) []int {
	var x []int
	for k := range m.All() {
		x = append(x, k)
	}
	return x
}

func TestDepth(t *testing.T) {
	t.Skip("depth")
	test(t, func(t *testing.T, newMap func() Mapper[int, int]) {
		for _, mode := range []string{"seq", "rand"} {
			t.Run(mode, func(t *testing.T) {
				for range 3 {
					const N = 1000000
					m := newMap()
					if mode == "seq" {
						for i := range N {
							m.Set(i, i)
						}
					} else {
						for _, i := range rand.Perm(N) {
							m.Set(i, i)
						}
					}
					t.Logf("n=%d depth=%d", N, m.Depth())
				}
			})
		}
	})
}

func allPerm(n int) iter.Seq[[]int] {
	return func(yield func([]int) bool) {
		x := make([]int, n)
		for i := range x {
			x[i] = i
		}
		genAllPerm(n, x, yield)
	}
}

func genAllPerm(k int, x []int, yield func([]int) bool) bool {
	if k <= 1 {
		return yield(x)
	}
	if !genAllPerm(k-1, x, yield) {
		return false
	}
	for i := range k - 1 {
		if k%2 == 0 {
			x[i], x[k-1] = x[k-1], x[i]
		} else {
			x[0], x[k-1] = x[k-1], x[0]
		}
		if !genAllPerm(k-1, x, yield) {
			return false
		}
	}
	return true
}
