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

// A Map is a map[K]V ordered according to K's standard Go ordering.
// The zero value of a Map is an empty Map ready to use.
type llrbMap[K cmp.Ordered, V any] struct {
	llrb[K, V]
}

type llrb[K, V any] struct {
	root *rbnode[K, V]
}

type llrbMapFunc[K, V any] struct {
	llrb[K, V]
	cmp func(K, K) int
}

func (t *llrbMapFunc[K, V]) init(cmp func(K, K) int) {
	t.cmp = cmp
}

// An rbnode is a node in the LLRB tree.
type rbnode[K, V any] struct {
	parent *rbnode[K, V]
	left   *rbnode[K, V]
	right  *rbnode[K, V]
	red    bool
	del    bool
	key    K
	val    V
}

func (x *rbnode[K, V]) deleted() bool {
	return x.del
}

func (t *llrb[K, V]) Depth() int {
	return t.root.depth()
}

func (x *rbnode[K, V]) depth() int {
	if x == nil {
		return -1
	}
	return 1 + max(x.left.depth(), x.right.depth())
}

func (t *llrb[K, V]) setRoot(x *rbnode[K, V]) {
	t.root = x
	if x != nil {
		x.parent = nil
	}
}

func (x *rbnode[K, V]) setLeft(y *rbnode[K, V]) {
	x.left = y
	if y != nil {
		y.parent = x
	}
}

func (x *rbnode[K, V]) setRight(y *rbnode[K, V]) {
	x.right = y
	if y != nil {
		y.parent = x
	}
}

func (m *llrbMap[K, V]) Get(key K) (val V, ok bool) {
	x := m.get(key)
	if x == nil {
		return
	}
	return x.val, true
}

func (m *llrbMap[K, V]) get(key K) *rbnode[K, V] {
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

func (m *llrbMapFunc[K, V]) Get(key K) (val V, ok bool) {
	x := m.get(key)
	if x == nil {
		return
	}
	return x.val, true
}

func (m *llrbMapFunc[K, V]) get(key K) *rbnode[K, V] {
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

func (x *rbnode[K, V]) isRed() bool {
	if x == nil {
		return false
	}
	return x.red
}

func (t *llrb[K, V]) replaceChild(p, old, x *rbnode[K, V]) {
	switch {
	case p == nil:
		if t.root != old {
			panic("corrupt llrb")
		}
		t.setRoot(x)
	case p.left == old:
		p.setLeft(x)
	case p.right == old:
		p.setRight(x)
	default:
		panic("corrupt llrb")
	}
}

// rotateRight rotates the subtree rooted at node y.
// turning (y (x a b) c) into (x a (y b c)).
func (t *llrb[K, V]) rotateRight(y *rbnode[K, V]) *rbnode[K, V] {
	//m.Rotates++
	// p -> (y (x a b) c)
	p := y.parent
	x := y.left
	b := x.right

	x.setRight(y)
	y.setLeft(b)
	t.replaceChild(p, y, x)

	x.red = y.red
	y.red = true

	return x
}

// rotateLeft rotates the subtree rooted at node x.
// turning (x a (y b c)) into (y (x a b) c).
func (t *llrb[K, V]) rotateLeft(x *rbnode[K, V]) *rbnode[K, V] {
	//m.Rotates++
	// p -> (x a (y b c))
	p := x.parent
	y := x.right
	b := y.left

	y.setLeft(x)
	x.setRight(b)
	t.replaceChild(p, x, y)

	y.red = x.red
	x.red = true

	return y
}

func (t *llrb[K, V]) flipColors(x *rbnode[K, V]) {
	x.red = !x.red
	x.left.red = !x.left.red
	x.right.red = !x.right.red
}

func (m *llrbMap[K, V]) checkAll() {
	defer func() {
		if e := recover(); e != nil {
			println(m.Dump())
			panic(e)
		}
	}()
	m.root.checkAll(cmp.Compare[K])
}

func (m *llrbMapFunc[K, V]) checkAll() {
	defer func() {
		if e := recover(); e != nil {
			println(m.Dump())
			panic(e)
		}
	}()
	m.root.checkAll(m.cmp)
}

func (x *rbnode[K, V]) checkAll(cmp func(K, K) int) int {
	if x == nil {
		return -1
	}
	if x.left != nil && cmp(x.left.key, x.key) >= 0 {
		panic("bad left order")
	}
	if x.left != nil && x.left.parent != x {
		println("P", x.key, x.left.key, x.left.parent.key)
		panic("bad left parent")
	}
	if x.right != nil && cmp(x.key, x.right.key) >= 0 {
		panic("bad right order")
	}
	if x.right != nil && x.right.parent != x {
		panic("bad right parent")
	}
	if x.red && x.left != nil && x.left.red {
		panic("bad llrb double red left")
	}
	if x.red && x.right != nil && x.right.red {
		panic("bad llrb double red right")
	}
	if x.right.isRed() {
		panic("bad llrb right red")
	}
	h1 := x.left.checkAll(cmp)
	h2 := x.right.checkAll(cmp)
	if h1 != h2 {
		panic("bad llrb height")
	}
	if !x.red {
		h1++
	}
	return h1
}

func (t *llrb[K, V]) recolorUp(x *rbnode[K, V]) {
	for x != nil {
		if x.right.isRed() && !x.left.isRed() {
			x = t.rotateLeft(x)
		}
		if x.left.isRed() && x.left.left.isRed() {
			x = t.rotateRight(x)
		}
		if x.left.isRed() && x.right.isRed() {
			t.flipColors(x)
		}
		x = x.parent
	}
	if t.root != nil {
		t.root.red = false
	}
}

func (m *llrbMap[K, V]) Set(key K, val V) {
	pos, parent := m.locate(key)
	m.set(key, val, pos, parent)
	m.checkAll()
}

func (m *llrbMapFunc[K, V]) Set(key K, val V) {
	pos, parent := m.locate(key)
	m.set(key, val, pos, parent)
}

func (t *llrb[K, V]) set(key K, val V, pos **rbnode[K, V], parent *rbnode[K, V]) {
	if x := *pos; x != nil {
		x.val = val
		return
	}
	x := &rbnode[K, V]{key: key, val: val, parent: parent, red: true}
	*pos = x
	t.recolorUp(x)
}

// Delete deletes m[key].
func (m *llrbMap[K, V]) Delete(key K) {
	m.delete(key, cmp.Compare[K])
	m.checkAll()
}

// Delete deletes m[key].
func (m *llrbMapFunc[K, V]) Delete(key K) {
	m.delete(key, m.cmp)
	m.checkAll()
}

func (t *llrb[K, V]) delete(key K, cmp func(K, K) int) {
	pos, parent, x := &t.root, t.root, t.root
	if x == nil {
		return
	}
	for {
		if x == nil {
			t.recolorUp(parent)
			return
		}
		if cmp(key, x.key) < 0 {
			if !x.left.isRed() && x.left != nil && !x.left.left.isRed() { // TODO x.left != nil?
				x = t.moveRedLeft(x)
			}
			parent, pos, x = x, &x.left, x.left
		} else {
			if x.left.isRed() {
				x = t.rotateRight(x)
			}
			if cmp(key, x.key) == 0 && x.right == nil {
				*pos = nil
				t.recolorUp(parent)
				break
			}
			if !x.right.isRed() && x.right != nil && !x.right.left.isRed() {
				x = t.moveRedRight(x)
			}
			if cmp(key, x.key) == 0 {
				z, zparent := t.deleteMin(&x.right)
				if zparent == x {
					zparent = z
				}
				z.setLeft(x.left)
				z.setRight(x.right)
				z.red = x.red
				t.replaceChild(x.parent, x, z)
				t.recolorUp(zparent)
				break
			}
			parent, pos, x = x, &x.right, x.right
		}
	}

	x.parent = nil
	x.left = nil
	x.right = nil
	x.del = true
}

func (m *llrbMap[K, V]) locate(key K) (pos **rbnode[K, V], parent *rbnode[K, V]) {
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

func (t *llrb[K, V]) moveRedLeft(x *rbnode[K, V]) *rbnode[K, V] {
	t.flipColors(x)
	if x.right != nil && x.right.left.isRed() {
		t.rotateRight(x.right)
		x = t.rotateLeft(x)
		t.flipColors(x)
	}
	return x
}

func (t *llrb[K, V]) moveRedRight(x *rbnode[K, V]) *rbnode[K, V] {
	t.flipColors(x)
	if x.left != nil && x.left.left != nil && x.left.left.red {
		x = t.rotateRight(x)
		t.flipColors(x)
	}
	return x
}

func (m *llrbMapFunc[K, V]) locate(key K) (pos **rbnode[K, V], parent *rbnode[K, V]) {
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

func (t *llrbMap[K, V]) split(key K) (x *rbnode[K, V], after llrb[K, V]) {
	return t.llrb.split(key, cmp.Compare[K])
}

func (t *llrbMapFunc[K, V]) split(key K) (x *rbnode[K, V], after llrb[K, V]) {
	return t.llrb.split(key, t.cmp)
}

func (t *llrb[K, V]) split(key K, cmp func(K, K) int) (x *rbnode[K, V], after llrb[K, V]) {
	panic("split")
	/*
		//  split(T,k) =
		//    if T = Leaf then (Leaf, false, Leaf)
		//    else
		//      (L,m,R) = expose(T)
		//      if k = m then (L, true, R)
		//      else if k < m then
		//        (LL, b, LR) = split(L, k)
		//        (LL, b, join(LR, m, R))
		//      else
		//        (RL, b, RR) = split(R, k)
		//        (join(L, m, RL), b, RR)
		//
		//  (Figure 1)
		right := llrb[K, V]{}
		if t.root == nil {
			return nil, right
		}

		mid := t.root
		t.setRoot(mid.left)
		right.setRoot(mid.right)
		mid.left, mid.right = nil, nil

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
	*/
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

func (t *llrb[K, V]) min() **rbnode[K, V] {
	pos, x := &t.root, t.root
	for x != nil && x.left != nil {
		pos, x = &x.left, x.left
	}
	return pos
}

func (t *llrb[K, V]) max() **rbnode[K, V] {
	pos, x := &t.root, t.root
	for x != nil && x.right != nil {
		pos, x = &x.right, x.right
	}
	return pos
}

/*
func (t *llrb[K, V]) join(y *rbnode[K, V], after llrb[K, V]) {
	if y == nil {
		pos := after.min()
		y = *pos
		if y == nil {
			return
		}
		after.delete(pos)
	}

	if y.left != nil || y.right != nil || y.height >= 0 {
		panic("llrb join misuse")
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
		t.recolorUp(y)

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
		t.recolorUp(y)

	default:
		y.setLeft(x)
		y.setRight(z)
		t.setRoot(y)
		t.recolorUp(y)
	}

	after.root = nil
	t.recolorUp(y)
}

func (m *llrbMap[K, V]) Split(key K) (val V, ok bool, more llrb[K, V]) {
	mid, more := m.split(key)
	if mid != nil {
		val, ok = mid.val, true
	}
	return val, ok, more
}
*/

func (t *llrb[K, V]) deleteMin(zpos **rbnode[K, V]) (z, zparent *rbnode[K, V]) {
	//fmt.Println("before deleteMin:", t.Dump())
	z = *zpos
	for {
		if z.left == nil {
			zparent = z.parent
			if z.right != nil {
				panic("bad z.right")
			}
			*zpos = nil
			//fmt.Println("after deleteMin:", t.Dump())
			return z, zparent
		}
		if !z.left.isRed() && !z.left.left.isRed() {
			z = t.moveRedLeft(z)
		}
		zpos, z = &z.left, z.left
	}
}

func (root *rbnode[K, V]) dump() string {
	var buf bytes.Buffer
	var walk func(*rbnode[K, V])
	walk = func(x *rbnode[K, V]) {
		if x == nil {
			fmt.Fprintf(&buf, "nil")
			return
		}
		fmt.Fprintf(&buf, "(")
		if x.red {
			fmt.Fprintf(&buf, "RED ")
		}
		fmt.Fprintf(&buf, "%v:%v", x.key, x.val)
		if x.left != nil || x.right != nil {
			fmt.Fprintf(&buf, " ")
			walk(x.left)
			fmt.Fprintf(&buf, " ")
			walk(x.right)
		}
		fmt.Fprintf(&buf, ")")
	}
	walk(root)
	return buf.String()
}

func (t *llrbMap[K, V]) DeleteRange(lo, hi K) {
	if t == nil {
		panic("nil DeleteRange")
	}
	if lo > hi {
		return
	}
	t.deleteRange(lo, hi, t.split)
}

func (t *llrbMapFunc[K, V]) DeleteRange(lo, hi K) {
	if t == nil {
		panic("nil DeleteRange")
	}
	if t.cmp(lo, hi) > 0 {
		return
	}
	t.deleteRange(lo, hi, t.split)
}

func (t *llrb[K, V]) deleteRange(lo, hi K, split func(K) (*rbnode[K, V], llrb[K, V])) {
	panic("deleteRange")
	/*
		_, after := split(hi)
		_, middle := split(lo)
		t.join(nil, after)
		middle.root.markDeleted()
	*/
}

/*
func (x *rbnode[K, V]) markDeleted() {
	if x == nil {
		return
	}
	x.height = -1
	x.left.markDeleted()
	x.right.markDeleted()
}
*/

// All returns an iterator over the map m.
// If m is modified during the iteration, some keys may not be visited.
// No keys will be visited multiple times.
func (m *llrbMap[K, V]) All() iter.Seq2[K, V] {
	return m.all(m.locate)
}

// All returns an iterator over the map m.
// If m is modified during the iteration, some keys may not be visited.
// No keys will be visited multiple times.
func (m *llrbMapFunc[K, V]) All() iter.Seq2[K, V] {
	return m.all(m.locate)
}

func (t *llrb[K, V]) all(locate func(K) (**rbnode[K, V], *rbnode[K, V])) iter.Seq2[K, V] {
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
			if x.deleted() {
				x = t.nextAfter(locate(x.key))
			} else {
				x = x.next()
			}
		}
	}
}

func (x *rbnode[K, V]) next() *rbnode[K, V] {
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

func (t *llrb[K, V]) nextAfter(pos **rbnode[K, V], parent *rbnode[K, V]) *rbnode[K, V] {
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
func (m *llrbMap[K, V]) Scan(lo, hi K) iter.Seq2[K, V] {
	return m.scan(lo, hi, cmp.Compare[K], m.locate)
}

// Scan returns an iterator over the map m
// limited to keys k satisfying lo ≤ k ≤ hi.
//
// If m is modified during the iteration, some keys may not be visited.
// No keys will be visited multiple times.
func (m *llrbMapFunc[K, V]) Scan(lo, hi K) iter.Seq2[K, V] {
	return m.scan(lo, hi, m.cmp, m.locate)
}

func (t *llrb[K, V]) scan(lo, hi K, cmp func(K, K) int, locate func(K) (**rbnode[K, V], *rbnode[K, V])) iter.Seq2[K, V] {
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
			if x.deleted() {
				x = t.nextAfter(locate(x.key))
			} else {
				x = x.next()
			}
		}
	}
}

func (t *llrb[K, V]) Dump() string {
	return t.root.dump()
}
