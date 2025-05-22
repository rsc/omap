// Copyright 2024 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package omap

import (
	"bytes"
	"cmp"
	"fmt"
	"iter"
)

// In-memory database stored as self-balancing AVL tree.
// See Lewis & Denenberg, Data Structures and Their Algorithms.

// A Map is a map[K]V ordered according to K's standard Go ordering.
// The zero value of a Map is an empty Map ready to use.
type avlMap[K cmp.Ordered, V any] struct {
	avl[K, V]
}

type avl[K, V any] struct {
	root *anode[K, V]
}

type avlMapFunc[K, V any] struct {
	avl[K, V]
	cmp func(K, K) int
}

func (t *avlMapFunc[K, V]) init(cmp func(K, K) int) {
	t.cmp = cmp
}

// An anode is a node in the AVL tree.
type anode[K, V any] struct {
	parent *anode[K, V]
	left   *anode[K, V]
	right  *anode[K, V]
	bal    int
	height int
	key    K
	val    V
}

func (t *avl[K, V]) Depth() int {
	return t.root.safeHeight()
}

func (t *avl[K, V]) setRoot(x *anode[K, V]) {
	t.root = x
	if x != nil {
		x.parent = nil
	}
}

func (x *anode[K, V]) setLeft(y *anode[K, V]) {
	x.left = y
	if y != nil {
		y.parent = x
	}
}

func (x *anode[K, V]) setRight(y *anode[K, V]) {
	x.right = y
	if y != nil {
		y.parent = x
	}
}

func (m *avlMap[K, V]) Get(key K) (val V, ok bool) {
	x := m.get(key)
	if x == nil {
		return
	}
	return x.val, true
}

func (m *avlMap[K, V]) get(key K) *anode[K, V] {
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

func (m *avlMapFunc[K, V]) Get(key K) (val V, ok bool) {
	x := m.get(key)
	if x == nil {
		return
	}
	return x.val, true
}

func (m *avlMapFunc[K, V]) get(key K) *anode[K, V] {
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

func (n *anode[K, V]) safeHeight() int {
	if n == nil {
		return -1
	}
	return n.height
}

func (n *anode[K, V]) checkbal() {
	b := n.right.safeHeight() - n.left.safeHeight()
	if b != n.bal {
		println("bad balance", n.left.safeHeight(), n.right.safeHeight(), b, n.bal, n.dump())
		panic("bad balance")
	}
}

func (n *anode[K, V]) setHeight() {
	n.height = 1 + max(n.left.safeHeight(), n.right.safeHeight())
}

func (n *anode[K, V]) setbal() {
	n.bal = n.right.safeHeight() - n.left.safeHeight()
}

func (t *avl[K, V]) replaceChild(p, old, x *anode[K, V]) {
	switch {
	case p == nil:
		if t.root != old {
			panic("corrupt avl")
		}
		t.setRoot(x)
	case p.left == old:
		p.setLeft(x)
	case p.right == old:
		p.setRight(x)
	default:
		panic("corrupt avl")
	}
}

func (t *avl[K, V]) rebalanceUp(x *anode[K, V]) {
	for x != nil {
		h := x.height
		x.setHeight()
		x.setbal()
		switch x.bal {
		case -2:
			if x.left.bal == 1 {
				t.rotateLeft(x.left)
			}
			x = t.rotateRight(x)

		case +2:
			if x.right.bal == -1 {
				t.rotateRight(x.right)
			}
			x = t.rotateLeft(x)
		}
		if x.height == h {
			return
		}
		x = x.parent
	}
}

// rotateRight rotates the subtree rooted at node y.
// turning (y (x a b) c) into (x a (y b c)).
func (t *avl[K, V]) rotateRight(y *anode[K, V]) *anode[K, V] {
	//m.Rotates++
	// p -> (y (x a b) c)
	p := y.parent
	x := y.left
	b := x.right

	x.checkbal()
	y.checkbal()

	x.setRight(y)
	y.setLeft(b)
	t.replaceChild(p, y, x)

	y.setHeight()
	y.setbal()
	x.setHeight()
	x.setbal()
	return x
}

// rotateLeft rotates the subtree rooted at node x.
// turning (x a (y b c)) into (y (x a b) c).
func (t *avl[K, V]) rotateLeft(x *anode[K, V]) *anode[K, V] {
	//m.Rotates++
	// p -> (x a (y b c))
	p := x.parent
	y := x.right
	b := y.left

	x.checkbal()
	y.checkbal()

	y.setLeft(x)
	x.setRight(b)
	t.replaceChild(p, x, y)

	x.setHeight()
	x.setbal()
	y.setHeight()
	y.setbal()
	return y
}

func (m *avlMap[K, V]) Set(key K, val V) {
	pos, parent := m.locate(key)
	m.set(key, val, pos, parent)
}

func (m *avlMapFunc[K, V]) Set(key K, val V) {
	pos, parent := m.locate(key)
	m.set(key, val, pos, parent)
}

func (t *avl[K, V]) set(key K, val V, pos **anode[K, V], parent *anode[K, V]) {
	if x := *pos; x != nil {
		x.val = val
		return
	}
	x := &anode[K, V]{key: key, val: val, parent: parent, height: -1}
	*pos = x
	t.rebalanceUp(x)
}

// Delete deletes m[key].
func (m *avlMap[K, V]) Delete(key K) {
	pos, _ := m.locate(key)
	m.delete(pos)
}

// Delete deletes m[key].
func (m *avlMapFunc[K, V]) Delete(key K) {
	pos, _ := m.locate(key)
	m.delete(pos)
}

func (t *avl[K, V]) delete(pos **anode[K, V]) {
	t.root.checkParents(nil)

	x := *pos
	switch {
	case x == nil:
		return

	case x.left == nil:
		if *pos = x.right; *pos != nil {
			(*pos).parent = x.parent
		}
		t.rebalanceUp(x.parent)

	case x.right == nil:
		*pos = x.left
		x.left.parent = x.parent
		t.rebalanceUp(x.parent)

	default:
		t.deleteSwap(pos)
	}

	x.bal = -100
	x.parent = nil
	x.left = nil
	x.right = nil
	x.height = -1
	t.root.checkParents(nil)
}

func (m *avlMap[K, V]) locate(key K) (pos **anode[K, V], parent *anode[K, V]) {
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

func (m *avlMapFunc[K, V]) locate(key K) (pos **anode[K, V], parent *anode[K, V]) {
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

func (t *avlMap[K, V]) split(key K) (x *anode[K, V], after avl[K, V]) {
	return t.avl.split(key, cmp.Compare[K])
}

func (t *avlMapFunc[K, V]) split(key K) (x *anode[K, V], after avl[K, V]) {
	return t.avl.split(key, t.cmp)
}

func (t *avl[K, V]) split(key K, cmp func(K, K) int) (x *anode[K, V], after avl[K, V]) {
	/*
	   split(T,k) =
	     if T = Leaf then (Leaf, false, Leaf)
	     else
	       (L,m,R) = expose(T)
	       if k = m then (L, true, R)
	       else if k < m then
	         (LL, b, LR) = split(L, k)
	         (LL, b, join(LR, m, R))
	       else
	         (RL, b, RR) = split(R, k)
	         (join(L, m, RL), b, RR)

	   (Figure 1)
	*/
	right := avl[K, V]{}
	if t.root == nil {
		return nil, right
	}

	mid := t.root
	t.setRoot(mid.left)
	right.setRoot(mid.right)
	mid.left, mid.right, mid.height = nil, nil, -1

	c := cmp(key, mid.key)
	if c == 0 {
		return mid, right
	}
	if c < 0 {
		leftMid, leftRight := t.split(key, cmp)
		leftRight.join(mid, right)
		return leftMid, leftRight
	}
	if c > 0 {
		rightMid, rightRight := right.split(key, cmp)
		t.join(mid, right)
		return rightMid, rightRight
	}
	panic("unreachable")
}

/*
join(TL, k, TR) =
  if h(TL) > h(TR)+1 then joinRight(TL, k, TR)
  else if h(TR) > h(TL)+1 then joinLeft(TL,k,TR)
  else Node(TL, k, TR)

joinRight(TL, k, TR) =
  (l, k', c) = expose(TL)
  if h(c) <= h(TR)+1 then
    T' = Node(c,k,TR)
    if h(T') <= h(l)+1 then Node(l,k',T')
    else rotateLeft(Node(l,k',rotateRight(T'))
  else
    T' = joinRight(c,k,TR)
    T'' = Node(l,k',T')
    if h(T') <= h(l)+1 then T''
    else rotateLeft(T'')

(Figure 2)

split(T,k) =
  if T = Leaf then (Leaf, false, Leaf)
  else
    (L,m,R) = expose(T)
    if k = m then (L, true, R)
    else if k < m then
      (LL, b, LR) = split(L, k)
      (LL, b, join(LR, m, R))
    else
      (RL, b, RR) = split(R, k)
      (join(L, m, RL), b, RR)

(Figure 1)

https://arxiv.org/pdf/1602.02120
*/

func (t *avl[K, V]) min() **anode[K, V] {
	pos, x := &t.root, t.root
	for x != nil && x.left != nil {
		pos, x = &x.left, x.left
	}
	return pos
}

func (t *avl[K, V]) max() **anode[K, V] {
	pos, x := &t.root, t.root
	for x != nil && x.right != nil {
		pos, x = &x.right, x.right
	}
	return pos
}

func (t *avl[K, V]) join(y *anode[K, V], after avl[K, V]) {
	if y == nil {
		pos := after.min()
		y = *pos
		if y == nil {
			return
		}
		after.delete(pos)
	}

	if y.left != nil || y.right != nil || y.height >= 0 {
		panic("avl join misuse")
	}

	x := t.root
	z := after.root
	xh := x.safeHeight()
	zh := z.safeHeight()

	switch {
	case xh > zh+1:
		for x.right != nil && x.right.height > zh {
			x = x.right
		}
		// now x.height > zh but x.right.height <= zh
		// replacing x.right with y=node{x.right, z} will grow x.right.height at most 1
		// println("JOIN X", x.safeHeight(), x.left.safeHeight(), x.right.safeHeight(), z.safeHeight())
		y.setLeft(x.right)
		y.setRight(z)
		x.setRight(y)
		y.height = -1
		t.rebalanceUp(y)
		t.root.checkAll()

	case zh > xh+1:
		for z.left != nil && z.left.height > xh {
			z = z.left
		}
		// println("JOIN Z", z.safeHeight(), z.left.safeHeight(), z.right.safeHeight(), x.safeHeight())
		y.setLeft(x)
		y.setRight(z.left)
		z.setLeft(y)
		y.height = -1
		t.root = after.root
		t.rebalanceUp(y)
		t.root.checkAll()

	default:
		y.setLeft(x)
		y.setRight(z)
		t.setRoot(y)
		t.rebalanceUp(y)
		t.root.checkAll()
	}

	after.root = nil
	t.rebalanceUp(y)
}

func (m *avlMap[K, V]) Split(key K) (val V, ok bool, more avl[K, V]) {
	mid, more := m.split(key)
	if mid != nil {
		val, ok = mid.val, true
	}
	return val, ok, more
}

func (t *avl[K, V]) deleteMin(zpos **anode[K, V]) (z, zparent *anode[K, V]) {
	for (*zpos).left != nil {
		zpos = &(*zpos).left
	}
	z = *zpos
	zparent = z.parent
	*zpos = z.right
	if *zpos != nil {
		(*zpos).parent = zparent
	}
	return z, zparent
}

func (t *avl[K, V]) deleteSwap(pos **anode[K, V]) {
	x := *pos
	z, zparent := t.deleteMin(&x.right)

	*pos = z
	if zparent == x {
		zparent = z
	}
	z.parent = x.parent
	z.height = x.height
	z.bal = x.bal
	z.setLeft(x.left)
	z.setRight(x.right)

	t.rebalanceUp(zparent)
}

func (n *anode[K, V]) checkAll() {
	return
	if n == nil {
		return
	}
	if n.height != 1+max(n.left.safeHeight(), n.right.safeHeight()) {
		panic("bad height")
	}
	n.checkbal()
	n.left.checkAll()
	n.right.checkAll()
}

func (n *anode[K, V]) checkParents(p *anode[K, V]) {
	return
	if n == nil {
		return
	}
	if n.parent != p {
		panic("bad parent")
	}
	n.left.checkParents(n)
	n.right.checkParents(n)
	n.checkbal()
}

func (t *avlMap[K, V]) Dump() string {
	return t.root.dump()
}

func (root *anode[K, V]) dump() string {
	var buf bytes.Buffer
	var walk func(*anode[K, V])
	walk = func(x *anode[K, V]) {
		if x == nil {
			fmt.Fprintf(&buf, "nil")
			return
		}
		fmt.Fprintf(&buf, "(%d/%d %v:%v ", x.bal, x.height, x.key, x.val)
		walk(x.left)
		fmt.Fprintf(&buf, " ")
		walk(x.right)
		fmt.Fprintf(&buf, ")")
	}
	walk(root)
	return buf.String()
}

func (t *avlMap[K, V]) DeleteRange(lo, hi K) {
	if t == nil {
		panic("nil DeleteRange")
	}
	if lo > hi {
		return
	}
	t.deleteRange(lo, hi, t.split)
}

func (t *avlMapFunc[K, V]) DeleteRange(lo, hi K) {
	if t == nil {
		panic("nil DeleteRange")
	}
	if t.cmp(lo, hi) > 0 {
		return
	}
	t.deleteRange(lo, hi, t.split)
}

func (t *avl[K, V]) deleteRange(lo, hi K, split func(K) (*anode[K, V], avl[K, V])) {
	_, after := split(hi)
	_, middle := split(lo)
	t.join(nil, after)
	middle.root.markDeleted()
}

func (x *anode[K, V]) markDeleted() {
	if x == nil {
		return
	}
	x.height = -1
	x.left.markDeleted()
	x.right.markDeleted()
}

// All returns an iterator over the map m.
// If m is modified during the iteration, some keys may not be visited.
// No keys will be visited multiple times.
func (m *avlMap[K, V]) All() iter.Seq2[K, V] {
	return m.all(m.locate)
}

// All returns an iterator over the map m.
// If m is modified during the iteration, some keys may not be visited.
// No keys will be visited multiple times.
func (m *avlMapFunc[K, V]) All() iter.Seq2[K, V] {
	return m.all(m.locate)
}

func (t *avl[K, V]) all(locate func(K) (**anode[K, V], *anode[K, V])) iter.Seq2[K, V] {
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
			if x.height >= 0 {
				// still in tree
				x = x.next()
			} else {
				// deleted
				x = t.nextAfter(locate(x.key))
			}
		}
	}
}

func (x *anode[K, V]) next() *anode[K, V] {
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

func (t *avl[K, V]) nextAfter(pos **anode[K, V], parent *anode[K, V]) *anode[K, V] {
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
func (m *avlMap[K, V]) Scan(lo, hi K) iter.Seq2[K, V] {
	return m.scan(lo, hi, cmp.Compare[K], m.locate)
}

// Scan returns an iterator over the map m
// limited to keys k satisfying lo ≤ k ≤ hi.
//
// If m is modified during the iteration, some keys may not be visited.
// No keys will be visited multiple times.
func (m *avlMapFunc[K, V]) Scan(lo, hi K) iter.Seq2[K, V] {
	return m.scan(lo, hi, m.cmp, m.locate)
}

func (t *avl[K, V]) scan(lo, hi K, cmp func(K, K) int, locate func(K) (**anode[K, V], *anode[K, V])) iter.Seq2[K, V] {
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
			if x.height >= 0 {
				x = x.next()
			} else {
				x = t.nextAfter(locate(x.key))
			}
		}
	}
}

func (t *avl[K, V]) Dump() string {
	var buf bytes.Buffer
	var walk func(*anode[K, V])
	walk = func(x *anode[K, V]) {
		if x == nil {
			fmt.Fprintf(&buf, "nil")
			return
		}
		fmt.Fprintf(&buf, "(h%d/b%+d %v:%v ", x.height, x.bal, x.key, x.val)
		walk(x.left)
		fmt.Fprintf(&buf, " ")
		walk(x.right)
		fmt.Fprintf(&buf, ")")
	}
	walk(t.root)
	return buf.String()

}
