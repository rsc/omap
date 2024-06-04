// Copyright 2024 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build go1.23

package omap

import (
	"bytes"
	"fmt"
	"math/rand/v2"
	"slices"
	"testing"
)

func Test(t *testing.T) {
	for range 10 {
		const N = 10
		var tr Map[int, int]
		perm := rand.Perm(N)
		inv := make([]int, N)
		for i, x := range perm {
			tr.Set(x, i)
			inv[x] = i
		}

		if false { // print treap
			var buf bytes.Buffer
			var walk func(*node[int, int])
			walk = func(x *node[int, int]) {
				if x == nil {
					fmt.Fprintf(&buf, "nil")
					return
				}
				fmt.Fprintf(&buf, "(%d ", x.key)
				walk(x.prev)
				fmt.Fprintf(&buf, " ")
				walk(x.next)
				fmt.Fprintf(&buf, ")")
			}
			walk(tr.root)
			t.Logf("treap: %s", buf.String())
		}

		for i, x := range perm {
			v, ok := tr.Get(x)
			if v != i || !ok {
				t.Errorf("Get(%d) = %d, %v, want %d, true", x, v, ok, i)
			}
		}

		var all []int
		for k, v := range tr.All() {
			if v != inv[k] {
				t.Errorf("All() returned %d, %d want %d, %d", k, v, k, inv[k])
			}
			all = append(all, k)
			if len(all) > N+5 {
				break
			}
		}
		if !match(all, 0, N-1) {
			t.Errorf("All() = %v, want 0..%d", all, N-1)
		}
		for lo := -1; lo <= N; lo++ {
			for hi := lo; hi <= N; hi++ {
				var scan []int
				for k, v := range tr.Scan(lo, hi) {
					if v != inv[k] {
						t.Errorf("Scan() returned %d, %d want %d, %d", k, v, k, inv[k])
					}
					scan = append(scan, k)
					if len(scan) > N+5 {
						break
					}
				}
				if !match(scan, max(lo, 0), min(hi, N-1)) {
					t.Errorf("Scan(%d, %d) = %v, want %d..%d", lo, hi, scan, lo, hi)
				}
			}
		}

		for i, x := range perm {
			tr.Delete(x)
			var list []int
			for k, _ := range tr.All() {
				list = append(list, k)
			}
			want := slices.Clone(perm[i+1:])
			slices.Sort(want)
			if !slices.Equal(list, want) {
				t.Errorf("after Delete [%v], All() = %v, want %v", perm[:i+1], list, want)
			}
		}
	}
}

func match(xs []int, lo, hi int) bool {
	if len(xs) != hi+1-lo {
		return false
	}
	for i, x := range xs {
		if x != lo+i {
			return false
		}
	}
	return true
}
