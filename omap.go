// Copyright 2024 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package omap implements in-memory ordered maps.
// [Map][K, V] is suitable for ordered types K,
// while [MapFunc][K, V] supports arbitrary keys and comparison functions.
package omap

// The implementation is a treap. See:
// https://en.wikipedia.org/wiki/Treap
// https://faculty.washington.edu/aragon/pubs/rst89.pdf

import (
	"cmp"
	"iter"
	"math/rand/v2"
)

// A Map is a map[K]V ordered according to K's standard Go ordering.
// The zero value of a Map is an empty Map ready to use.
type Map[K cmp.Ordered, V any] struct {
	root *node[K, V]
}

// A MapFunc is a map[K]V ordered according to an arbitrary comparison function.
// The zero value of a MapFunc is not meaningful since it has no comparison function.
// Use [NewMapFunc] to create a [MapFunc].
type MapFunc[K, V any] struct {
	root *node[K, V]
	cmp  func(K, K) int
}

// NewMapFunc returns a new MapFunc[K, V] ordered according to cmp.
func NewMapFunc[K, V any](cmp func(K, K) int) *MapFunc[K, V] {
	return &MapFunc[K, V]{cmp: cmp}
}

// A node is a node in the treap.
type node[K any, V any] struct {
	parent *node[K, V]
	prev   *node[K, V]
	next   *node[K, V]
	key    K
	val    V
	pri    uint64
}

// lookup looks up the key k in the map.
// It returns the parent of k as well as the position where k would be attached.
// *pos is non-nil if k is present, nil if k is missing.
// parent is nil if there are no nodes in the map, or if there is only one node and it's k.
func (m *Map[K, V]) lookup(k K) (parent *node[K, V], pos **node[K, V]) {
	pos = &m.root
	for x := *pos; x != nil; x = *pos {
		if x.key == k {
			break
		}
		parent = x
		if x.key > k {
			pos = &x.prev
		} else {
			pos = &x.next
		}
	}
	return parent, pos
}

// lookup is the same as for Map[K, V] but using m.cmp.
func (m *MapFunc[K, V]) lookup(k K) (parent *node[K, V], pos **node[K, V]) {
	pos = &m.root
	for x := *pos; x != nil; x = *pos {
		cmp := m.cmp(x.key, k)
		if cmp == 0 {
			break
		}
		parent = x
		if cmp > 0 {
			pos = &x.prev
		} else {
			pos = &x.next
		}
	}
	return parent, pos
}

// Set sets m[key] = val.
func (m *Map[K, V]) Set(key K, val V) {
	parent, pos := m.lookup(key)
	set(parent, pos, key, val, &m.root)
}

// Set sets m[key] = val.
func (m *MapFunc[K, V]) Set(key K, val V) {
	parent, pos := m.lookup(key)
	set(parent, pos, key, val, &m.root)
}

// set sets m[key] = val, where parent, pos are from m.lookup(k) and root is &m.root.
func set[K, V any](parent *node[K, V], pos **node[K, V], key K, val V, root **node[K, V]) {
	x := *pos
	if x != nil {
		x.val = val
		return
	}
	x = &node[K, V]{key: key, val: val, pri: rand.Uint64(), parent: parent}
	*pos = x

	// Rotate up into tree according to priority.
	for x.parent != nil && x.parent.pri > x.pri {
		if x.parent.prev == x {
			x.parent.rotateRight(root)
		} else if x.parent.next == x {
			x.parent.rotateLeft(root)
		} else {
			panic("corrupt treap")
		}
	}
}

// Delete deletes m[key].
func (m *Map[K, V]) Delete(key K) {
	_, pos := m.lookup(key)
	_delete(pos, &m.root)
}

// Delete deletes m[key].
func (m *MapFunc[K, V]) Delete(key K) {
	_, pos := m.lookup(key)
	_delete(pos, &m.root)
}

// _delete (not delete, to avoid shadowing builtin)
// deletes m[key], where pos is from m.lookup(key) and root is &m.root.
func _delete[K, V any](pos, root **node[K, V]) {
	x := *pos
	if x == nil {
		return
	}

	// Rotate x down to be leaf of tree for removal, respecting priorities.
	for x.next != nil || x.prev != nil {
		if x.next == nil || x.prev != nil && x.prev.pri < x.next.pri {
			x.rotateRight(root)
		} else {
			x.rotateLeft(root)
		}
	}

	// Remove x, now a leaf.
	if p := x.parent; p != nil {
		if p.prev == x {
			p.prev = nil
		} else {
			p.next = nil
		}
	} else {
		*root = nil
	}
}

// Get returns the value of m[key] and reports whether it exists.
func (m *Map[K, V]) Get(key K) (V, bool) {
	return get(m.lookup(key))
}

// Get returns the value of m[key] and reports whether it exists.
func (m *MapFunc[K, V]) Get(key K) (V, bool) {
	return get(m.lookup(key))
}

func get[K, V any](_ *node[K, V], pos **node[K, V]) (V, bool) {
	if *pos == nil {
		var zero V
		return zero, false
	}
	return (*pos).val, true
}

// All returns an iterator over the map m.
// If m is modified during the iteration, some keys may not be visited.
// No keys will be visited multiple times.
func (m *Map[K, V]) All() iter.Seq2[K, V] {
	return all(&m.root)
}

// All returns an iterator over the map m.
// If m is modified during the iteration, some keys may not be visited.
// No keys will be visited multiple times.
func (m *MapFunc[K, V]) All() iter.Seq2[K, V] {
	return all(&m.root)
}

// all returns an iterator over the map m, where *root is the root.
func all[K, V any](root **node[K, V]) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		x := *root
		if x != nil {
			for x.prev != nil {
				x = x.prev
			}
		}
		for x != nil && yield(x.key, x.val) {
			x = x.step()
		}
	}
}

// Scan returns an iterator over the map m
// limited to keys k satisfying lo ≤ k ≤ hi.
//
// If m is modified during the iteration, some keys may not be visited.
// No keys will be visited multiple times.
func (m *Map[K, V]) Scan(lo, hi K) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		parent, pos := m.lookup(lo)
		x := *pos
		if x == nil {
			x = parent
			if x.key < lo {
				x = x.step()
			}
		}
		for x != nil && x.key <= hi && yield(x.key, x.val) {
			x = x.step()
		}
	}
}

// Scan returns an iterator over the map m
// limited to keys k satisfying lo ≤ k ≤ hi.
//
// If m is modified during the iteration, some keys may not be visited.
// No keys will be visited multiple times.
func (m *MapFunc[K, V]) Scan(lo, hi K) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		parent, pos := m.lookup(lo)
		x := *pos
		if x == nil {
			x = parent
			if m.cmp(x.key, lo) < 0 {
				x = x.step()
			}
		}
		for x != nil && m.cmp(x.key, hi) <= 0 && yield(x.key, x.val) {
			x = x.step()
		}
	}
}

// step returns the successor node of x in the treap.
func (x *node[K, V]) step() *node[K, V] {
	if x == nil {
		panic("treap step nil")
	}
	if x.next == nil {
		for x.parent != nil && x.parent.next == x {
			x = x.parent
		}
		return x.parent
	}
	x = x.next
	for x.prev != nil {
		x = x.prev
	}
	return x
}

// rotateLeft rotates the subtree rooted at node x.
// turning (x a (y b c)) into (y (x a b) c).
func (x *node[K, V]) rotateLeft(root **node[K, V]) {
	// p -> (x a (y b c))
	p := x.parent
	y := x.next
	b := y.prev

	y.prev = x
	x.parent = y
	x.next = b
	if b != nil {
		b.parent = x
	}

	y.parent = p
	if p == nil {
		*root = y
	} else if p.prev == x {
		p.prev = y
	} else if p.next == x {
		p.next = y
	} else {
		panic("corrupt treap")
	}
}

// rotateRight rotates the subtree rooted at node y.
// turning (y (x a b) c) into (x a (y b c)).
func (y *node[K, V]) rotateRight(root **node[K, V]) {
	// p -> (y (x a b) c)
	p := y.parent
	x := y.prev
	b := x.next

	x.next = y
	y.parent = x
	y.prev = b
	if b != nil {
		b.parent = y
	}

	x.parent = p
	if p == nil {
		*root = x
	} else if p.prev == y {
		p.prev = x
	} else if p.next == y {
		p.next = x
	} else {
		panic("corrupt treap")
	}
}
