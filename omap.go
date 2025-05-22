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

import "cmp"

// A Map is a map[K]V ordered according to K's standard Go ordering.
// The zero value of a Map is an empty Map ready to use.
type Map[K cmp.Ordered, V any] struct {
	treapMap[K, V]
}

func (m *Map[K, V]) Join(more *Map[K, V]) {
	m.join(nil, more.treap)
	more.root = nil
}

func (m *Map[K, V]) Split(key K) (val V, ok bool, more *Map[K, V]) {
	x, after := m.split(key)
	if x != nil {
		val, ok = x.val, true
	}
	more = &Map[K, V]{treapMap[K, V]{after}}
	return val, ok, more
}

type MapFunc[K, V any] struct {
	treapMapFunc[K, V]
}

func NewMapFunc[K, V any](cmp func(K, K) int) *MapFunc[K, V] {
	m := new(MapFunc[K, V])
	m.cmp = cmp
	return m
}

func (m *MapFunc[K, V]) Join(more *MapFunc[K, V]) {
	m.join(nil, more.treap)
	more.root = nil
}

func (m *MapFunc[K, V]) Split(key K) (val V, ok bool, more *MapFunc[K, V]) {
	x, after := m.split(key)
	if x != nil {
		val, ok = x.val, true
	}
	more = &MapFunc[K, V]{treapMapFunc[K, V]{after, m.cmp}}
	return val, ok, more
}
