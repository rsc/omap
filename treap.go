// Copyright 2024 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package omap

import (
	"bytes"
	"cmp"
	"fmt"
	"iter"
	"math/rand/v2"
)

type treapMap[K cmp.Ordered, V any] struct {
	treap[K, V]
}

type treapMapFunc[K, V any] struct {
	treap[K, V]
	cmp func(K, K) int
}

func (t *treapMapFunc[K, V]) init(cmp func(K, K) int) {
	t.cmp = cmp
}

type treap[K, V any] struct {
	root *treapNode[K, V]
	// Rotates int
}

type treapNode[K, V any] struct {
	parent *treapNode[K, V]
	left   *treapNode[K, V]
	right  *treapNode[K, V]
	key    K
	val    V
	pri    uint64
}

func (t *treap[K, V]) setRoot(x *treapNode[K, V]) {
	t.root = x
	if x != nil {
		x.parent = nil
	}
}

func (x *treapNode[K, V]) setLeft(y *treapNode[K, V]) {
	x.left = y
	if y != nil {
		y.parent = x
	}
}

func (x *treapNode[K, V]) setRight(y *treapNode[K, V]) {
	x.right = y
	if y != nil {
		y.parent = x
	}
}

func (m *treapMap[K, V]) Get(key K) (val V, ok bool) {
	x := m.get(key)
	if x == nil {
		return
	}
	return x.val, true
}

func (m *treapMap[K, V]) get(key K) *treapNode[K, V] {
	if m == nil {
		return nil
	}
	x := m.root
	for x != nil {
		if key == x.key {
			return x
		}
		if key < x.key {
			x = x.left
		} else {
			x = x.right
		}
	}
	return nil
}

func (m *treapMapFunc[K, V]) Get(key K) (val V, ok bool) {
	x := m.get(key)
	if x == nil {
		return
	}
	return x.val, true
}

func (m *treapMapFunc[K, V]) get(key K) *treapNode[K, V] {
	if m == nil {
		return nil
	}
	x := m.root
	for x != nil {
		c := m.cmp(key, x.key)
		if c == 0 {
			return x
		}
		if c < 0 {
			x = x.left
		} else {
			x = x.right
		}
	}
	return nil
}

// Delete deletes m[key].
func (m *treapMap[K, V]) Delete(key K) {
	m.delete(m.get(key))
}

// Delete deletes m[key].
func (m *treapMapFunc[K, V]) Delete(key K) {
	m.delete(m.get(key))
}

func (t *treap[K, V]) delete(x *treapNode[K, V]) {
	if t == nil {
		panic("Delete of nil Map")
	}
	if x == nil {
		return
	}

	// Rotate x down to be leaf of tree for removal, respecting priorities.
	for x.right != nil || x.left != nil {
		if x.right == nil || x.left != nil && x.left.pri < x.right.pri {
			t.rotateRight(x)
		} else {
			t.rotateLeft(x)
		}
	}

	// Remove x, now a leaf.
	switch p := x.parent; {
	case p == nil:
		t.root = nil
	case p.left == x:
		p.left = nil
	default:
		p.right = nil
	}
	x.pri = 0 // mark deleted
}

// rotateUp rotates x upward in the tree to correct any priority inversions.
func (t *treap[K, V]) rotateUp(x *treapNode[K, V]) {
	// Rotate up into tree according to priority.
	for x.parent != nil && x.parent.pri > x.pri {
		if x.parent.left == x {
			t.rotateRight(x.parent)
		} else {
			t.rotateLeft(x.parent)
		}
	}
}

// rotateLeft rotates the subtree rooted at node x.
// turning (x a (y b c)) into (y (x a b) c).
func (t *treap[K, V]) rotateLeft(x *treapNode[K, V]) {
	// t.Rotates++
	// p -> (x a (y b c))
	p := x.parent
	y := x.right
	b := y.left

	y.left = x
	x.parent = y
	x.right = b
	if b != nil {
		b.parent = x
	}

	y.parent = p
	switch {
	case p == nil:
		t.root = y
	case p.left == x:
		p.left = y
	case p.right == x:
		p.right = y
	default:
		// unreachable
		panic("corrupt treap")
	}
}

// rotateRight rotates the subtree rooted at node y.
// turning (y (x a b) c) into (x a (y b c)).
func (t *treap[K, V]) rotateRight(y *treapNode[K, V]) {
	// t.Rotates++
	// p -> (y (x a b) c)
	p := y.parent
	x := y.left
	b := x.right

	x.right = y
	y.parent = x
	y.left = b
	if b != nil {
		b.parent = y
	}

	x.parent = p
	switch {
	case p == nil:
		t.root = x
	case p.left == y:
		p.left = x
	case p.right == y:
		p.right = x
	default:
		// unreachable
		panic("corrupt treap")
	}
}

func (m *treapMap[K, V]) Set(key K, val V) {
	pos, parent := m.locate(key)
	m.set(key, val, pos, parent)
}

func (m *treapMapFunc[K, V]) Set(key K, val V) {
	pos, parent := m.locate(key)
	m.set(key, val, pos, parent)
}

func (t *treap[K, V]) set(key K, val V, pos **treapNode[K, V], parent *treapNode[K, V]) {
	if x := *pos; x != nil {
		x.val = val
		return
	}
	x := &treapNode[K, V]{key: key, val: val, parent: parent, pri: rand.Uint64() | 1}
	*pos = x
	t.rotateUp(x)
}

func (m *treapMap[K, V]) locate(key K) (pos **treapNode[K, V], parent *treapNode[K, V]) {
	pos, x := &m.root, m.root
	for x != nil && key != x.key {
		parent = x
		if key < x.key {
			pos, x = &x.left, x.left
		} else {
			pos, x = &x.right, x.right
		}
	}
	return pos, parent
}

func (m *treapMapFunc[K, V]) locate(key K) (pos **treapNode[K, V], parent *treapNode[K, V]) {
	pos, x := &m.root, m.root
	for x != nil {
		c := m.cmp(key, x.key)
		if c == 0 {
			break
		}
		parent = x
		if c < 0 {
			pos, x = &x.left, x.left
		} else {
			pos, x = &x.right, x.right
		}
	}
	return pos, parent
}

func (t *treapMap[K, V]) split(key K) (x *treapNode[K, V], after treap[K, V]) {
	return t.treap.split(t.locate(key))
}

func (t *treapMapFunc[K, V]) split(key K) (x *treapNode[K, V], after treap[K, V]) {
	return t.treap.split(t.locate(key))
}

func (t *treap[K, V]) split(pos **treapNode[K, V], parent *treapNode[K, V]) (x *treapNode[K, V], after treap[K, V]) {
	clear := false
	x = *pos
	if x == nil {
		x = &treapNode[K, V]{parent: parent}
		*pos = x
		clear = true
	}
	x.pri = 0
	t.rotateUp(x)
	t.setRoot(x.left)
	after.setRoot(x.right)
	x.left, x.right = nil, nil
	if clear {
		x = nil
	}
	return x, after
}

func (t *treap[K, V]) min() *treapNode[K, V] {
	x := t.root
	for x != nil && x.left != nil {
		x = x.left
	}
	return x
}

func (t *treap[K, V]) max() *treapNode[K, V] {
	x := t.root
	for x != nil && x.right != nil {
		x = x.right
	}
	return x
}

func (t *treap[K, V]) join(x *treapNode[K, V], after treap[K, V]) {
	if x == nil {
		if x = after.min(); x == nil {
			return
		}
		after.delete(x)
	}
	if x.left != nil || x.right != nil || x.pri != 0 {
		panic("treap join misuse")
	}
	x.setRight(after.root)
	max := t.max()
	if max == nil {
		t.setRoot(x)
	} else {
		max.setRight(x)
	}
	if x.right != nil {
		t.rotateUp(x.right)
	} else {
		t.rotateUp(x)
	}
}

func (t *treapMap[K, V]) DeleteRange(lo, hi K) {
	if t == nil {
		panic("nil DeleteRange")
	}
	if lo > hi {
		return
	}
	t.deleteRange(lo, hi, t.split)
}

func (t *treapMapFunc[K, V]) DeleteRange(lo, hi K) {
	if t == nil {
		panic("nil DeleteRange")
	}
	if t.cmp(lo, hi) > 0 {
		return
	}
	t.deleteRange(lo, hi, t.split)
}

func (t *treap[K, V]) deleteRange(lo, hi K, split func(K) (*treapNode[K, V], treap[K, V])) {
	_, after := split(hi)
	_, middle := split(lo)
	t.join(nil, after)
	middle.root.markDeleted()
}

func (x *treapNode[K, V]) markDeleted() {
	if x == nil {
		return
	}
	x.pri = 0
	x.left.markDeleted()
	x.right.markDeleted()
}

func (t *treap[K, V]) Depth() int {
	return t.root.depth()
}

func (x *treapNode[K, V]) depth() int {
	if x == nil {
		return 0
	}
	return 1 + max(x.left.depth(), x.right.depth())
}

// All returns an iterator over the map m.
// If m is modified during the iteration, some keys may not be visited.
// No keys will be visited multiple times.
func (m *treapMap[K, V]) All() iter.Seq2[K, V] {
	return m.all(m.locate)
}

// All returns an iterator over the map m.
// If m is modified during the iteration, some keys may not be visited.
// No keys will be visited multiple times.
func (m *treapMapFunc[K, V]) All() iter.Seq2[K, V] {
	return m.all(m.locate)
}

func (t *treap[K, V]) all(locate func(K) (**treapNode[K, V], *treapNode[K, V])) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		if t == nil {
			return
		}
		x := t.root
		if x != nil {
			for x.left != nil {
				x = x.left
			}
		}
		for x != nil && yield(x.key, x.val) {
			if x.pri != 0 {
				// still in tree
				x = x.next()
			} else {
				// deleted
				x = t.nextAfter(locate(x.key))
			}
		}
	}
}

func (x *treapNode[K, V]) next() *treapNode[K, V] {
	if x.right == nil {
		for x.parent != nil && x.parent.right == x {
			x = x.parent
		}
		return x.parent
	}
	x = x.right
	for x.left != nil {
		x = x.left
	}
	return x
}

func (t *treap[K, V]) nextAfter(pos **treapNode[K, V], parent *treapNode[K, V]) *treapNode[K, V] {
	switch {
	case *pos != nil:
		return (*pos).next()
	case parent == nil:
		return nil
	case pos == &parent.left:
		return parent
	default:
		return parent.next()
	}
}

// Scan returns an iterator over the map m
// limited to keys k satisfying lo ≤ k ≤ hi.
//
// If m is modified during the iteration, some keys may not be visited.
// No keys will be visited multiple times.
func (m *treapMap[K, V]) Scan(lo, hi K) iter.Seq2[K, V] {
	return m.scan(lo, hi, cmp.Compare[K], m.locate)
}

// Scan returns an iterator over the map m
// limited to keys k satisfying lo ≤ k ≤ hi.
//
// If m is modified during the iteration, some keys may not be visited.
// No keys will be visited multiple times.
func (m *treapMapFunc[K, V]) Scan(lo, hi K) iter.Seq2[K, V] {
	return m.scan(lo, hi, m.cmp, m.locate)
}

func (t *treap[K, V]) scan(lo, hi K, cmp func(K, K) int, locate func(K) (**treapNode[K, V], *treapNode[K, V])) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		if t == nil {
			return
		}
		pos, parent := locate(lo)
		x := *pos
		if x == nil {
			x = t.nextAfter(pos, parent)
		}
		for x != nil && cmp(x.key, hi) <= 0 && yield(x.key, x.val) {
			if x.pri != 0 {
				x = x.next()
			} else {
				x = t.nextAfter(locate(x.key))
			}
		}
	}
}

func (t *treap[K, V]) Dump() string {
	var buf bytes.Buffer
	var walk func(*treapNode[K, V])
	walk = func(x *treapNode[K, V]) {
		if x == nil {
			fmt.Fprintf(&buf, "nil")
			return
		}
		fmt.Fprintf(&buf, "(%v:%v ", x.key, x.val)
		walk(x.left)
		fmt.Fprintf(&buf, " ")
		walk(x.right)
		fmt.Fprintf(&buf, ")")
	}
	walk(t.root)
	return buf.String()

}
