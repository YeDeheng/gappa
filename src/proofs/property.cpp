/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <algorithm>
#include <climits>
#include <new>
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "proofs/property.hpp"
#include "proofs/schemes.hpp"

typedef int long_is_not_long_enough_1[2 * (sizeof(long) >= sizeof(void *)) - 1];
typedef int long_is_not_long_enough_2[2 * (sizeof(long) >= sizeof(interval)) - 1];

property::property(): real() { store._int = 0; }

property::property(ast_real const *r): real(r, PRED_BND) {
  new(&store) interval;
}

property::property(ast_real const *r, interval const &i): real(r, PRED_BND) {
  new(&store) interval(i);
}

property::property(predicated_real const &r): real(r) {
  switch (real.pred()) {
  case PRED_ABS:
  case PRED_REL:
  case PRED_BND: new(&store) interval; break;
  case PRED_FIX: store._int = INT_MIN; break;
  case PRED_FLT: store._int = INT_MAX; break;
  case PRED_EQL:
  case PRED_NZR: break;
  }
}

property::property(predicated_real const &r, interval const &i): real(r) {
  assert(r.pred_bnd());
  new(&store) interval(i);
}

property::property(predicated_real const &r, long i): real(r)
{
  assert(r.pred_cst());
  store._int = i;
}

property::property(property const &p): real(p.real) {
  if (p.real.pred_bnd()) new(&store) interval(p._bnd());
  else store._int = p.store._int;
}

property::~property() {
  if (real.pred_bnd()) _bnd().~interval();
}

void property::clear()
{
  if (real.pred_bnd()) _bnd().~interval();
  real = predicated_real();
  store._int = 0;
}

property &property::operator=(property const &p) {
  if (p.real.pred_bnd()) {
    interval const &pb = p._bnd();
    if (real.pred_bnd()) _bnd() = pb;
    else new(&store) interval(pb);
  } else {
    if (real.pred_bnd()) _bnd().~interval();
    store._int = p.store._int;
  }
  real = p.real;
  return *this;
}

bool property::implies(property const &p) const {
  if (real != p.real) return false;
  switch (real.pred()) {
  case PRED_ABS:
  case PRED_REL:
  case PRED_BND: return _bnd() <= p._bnd();
  case PRED_FIX: return store._int >= p.store._int;
  case PRED_FLT: return store._int <= p.store._int;
  case PRED_EQL:
  case PRED_NZR: return true;
  }
  assert(false);
  return false;
}

bool property::strict_implies(property const &p) const {
  if (real != p.real) return false;
  switch (real.pred()) {
  case PRED_ABS:
  case PRED_REL:
  case PRED_BND: return _bnd() < p._bnd();
  case PRED_FIX: return store._int > p.store._int;
  case PRED_FLT: return store._int < p.store._int;
  case PRED_EQL:
  case PRED_NZR: return false;
  }
  assert(false);
  return false;
}

void property::intersect(property const &p) {
  assert(real == p.real);
  switch (real.pred()) {
  case PRED_ABS:
  case PRED_REL:
  case PRED_BND: _bnd() = ::intersect(_bnd(), p._bnd()); break;
  case PRED_FIX: store._int = std::max(store._int, p.store._int); break;
  case PRED_FLT: store._int = std::min(store._int, p.store._int); break;
  case PRED_EQL:
  case PRED_NZR: break;
  }
}

void property::hull(property const &p) {
  assert(real == p.real);
  switch (real.pred()) {
  case PRED_ABS:
  case PRED_REL:
  case PRED_BND: _bnd() = ::hull(_bnd(), p._bnd()); break;
  case PRED_FIX: store._int = std::min(store._int, p.store._int); break;
  case PRED_FLT: store._int = std::max(store._int, p.store._int); break;
  case PRED_EQL:
  case PRED_NZR: break;
  }
}

bool property::operator<(property const &r) const
{
  if (real != r.real) return real < r.real;
  if (real.pred_cst()) return store._int < r.store._int;
  if (!real.pred_bnd()) return false;
  if (!is_defined(_bnd())) return is_defined(r._bnd());
  return lower(_bnd()) < lower(r._bnd()) ||
    (lower(_bnd()) == lower(r._bnd()) && upper(_bnd()) < upper(r._bnd()));
}

bool property::operator==(property const &r) const
{
  if (real != r.real) return false;
  if (real.pred_cst()) return store._int == r.store._int;
  if (!real.pred_bnd()) return true;
  if (!is_defined(_bnd())) return !is_defined(_bnd());
  return lower(_bnd()) == lower(r._bnd()) && upper(_bnd()) == upper(r._bnd());
}

bool property_vect::implies(property_vect const &s) const {
  for(const_iterator i = s.begin(), i_end = s.end(); i != i_end; ++i) {
    bool implies_i = false;
    for(const_iterator j = begin(), j_end = end(); j != j_end; ++j)
      if (j->implies(*i)) { implies_i = true; break; }
    if (!implies_i) return false;
  }
  return true;
}

int property_vect::find_compatible_property(property const &p) const {
  for(const_iterator i_begin = begin(), i = i_begin, i_end = end(); i != i_end; ++i)
    if (i->implies(p)) return i - i_begin;
  return -1;
}

bool property_tree::operator<(property_tree const &t) const
{
  if (conjunction < t.conjunction) return true;
  if (conjunction != t.conjunction) return false;
  if (t.left) {
    if (!left) return true;
    if (*left < *t.left) return true;
    if (*left != *t.left) return false;
    return *right < *t.right;
  }
  if (left) return false;
  if (!t.atom) return false;
  if (!atom) return true;
  return *atom < *t.atom;
}

bool property_tree::operator==(property_tree const &t) const
{
  if (conjunction != t.conjunction) return false;
  if (t.left) {
    if (!left) return false;
    if (*left != *t.left) return false;
    return *right == *t.right;
  }
  if (left) return false;
  if (t.atom) {
    if (!atom) return false;
    return *atom == *t.atom;
  }
  return !atom;
}

property_tree::property_tree(property const &p)
  : conjunction(true), left(NULL), right(NULL), atom(new property(p))
{
}

property_tree::property_tree(property_tree const &t)
  : conjunction(t.conjunction), left(NULL), right(NULL), atom(NULL)
{
  if (t.atom) atom = new property(*t.atom);
  if (t.left) left = new property_tree(*t.left);
  if (t.right) right = new property_tree(*t.right);
}

property_tree::~property_tree()
{
  delete atom;
  delete left;
  delete right;
}

void property_tree::clear()
{
  delete atom; atom = NULL;
  delete left; left = NULL;
  delete right; right = NULL;
}

property_tree &property_tree::operator=(property_tree const &t)
{
  if (this == &t) return *this;
  clear();
  conjunction = t.conjunction;
  if (t.atom) atom = new property(*t.atom);
  if (t.left) left = new property_tree(*t.left);
  if (t.right) right = new property_tree(*t.right);
  return *this;
}

void property_tree::swap(property_tree &t)
{
  std::swap(conjunction, t.conjunction);
  std::swap(atom, t.atom);
  std::swap(left, t.left);
  std::swap(right, t.right);
}

/**
 * Returns a positive value if (not) @a p implies @a q, a negative value if
 * (not) @a p implies not @a q, zero otherwise.
 */
static int check_imply(bool positive, property const &p, property const &q)
{
  if (positive)
  {
    if (p.implies(q)) return 1;
    if (!p.real.pred_bnd()) return 0;
    property t = p;
    t.intersect(q);
    if (is_empty(t.bnd())) return -1;
  }
  else
  {
    if (q.implies(p)) return -1;
  }
  return 0;
}

int property_tree::try_simplify(property const &p, bool positive, undefined_map *force, bool &changed, property_tree &tgt) const
{
  assert(atom || left);
  changed = false;
  if (atom) {
    if (atom->real != p.real) return 0;
    property const *q = atom;
    if (atom->real.pred_bnd() && !is_defined(atom->bnd())) {
      // True by choice.
      assert(!conjunction);
      if (!force) return 0;
      undefined_map::iterator j = force->find(p.real);
      if (j != force->end()) {
        q = &j->second;
        goto def;
      }
      (*force)[p.real] = p;
      return -1;
    }
    def:
    if (int valid = check_imply(positive, p, *q)) {
      // From (not) p, one can deduce either i->first or not i->first.
      if (!conjunction) valid = -valid;
      return valid;
    }
    return 0;
  }
  bool chg1, chg2;
  property_tree t1;
  if (int valid = left->try_simplify(p, positive, force, chg1, t1)) {
    if ((valid > 0) ^ conjunction) return valid;
    valid = right->try_simplify(p, positive, force, chg2, tgt);
    if (!valid && !chg2) tgt = *right;
    changed = true;
    return valid;
  }
  property_tree t2;
  if (int valid = right->try_simplify(p, positive, force, chg2, t2)) {
    if ((valid > 0) ^ conjunction) return valid;
    if (chg1) tgt.swap(t1);
    else tgt = *left;
    changed = true;
    return 0;
  }
  if (!chg1 && !chg2) return 0;
  if (!chg1) t1 = *left;
  if (!chg2) t2 = *right;
  tgt.clear();
  tgt.left = new property_tree;
  tgt.right = new property_tree;
  tgt.left->swap(t1);
  tgt.right->swap(t2);
  changed = true;
  return 0;
}

int property_tree::simplify(property const &p)
{
  bool changed;
  property_tree t;
  int v = try_simplify(p, true, NULL, changed, t);
  if (v) {
    clear();
    conjunction = v > 0;
  } else if (changed) {
    swap(t);
  }
  return v;
}

void property_tree::negate()
{
  conjunction = !conjunction;
  if (left) {
    left->negate();
    right->negate();
  }
}

bool property_tree::verify(graph_t *g, property *p) const
{
  if (empty()) return false;
  graph_loader loader(g);
  if (atom) {
    if (find_proof(*atom, !conjunction)) return true;
    if (p) *p = *atom;
    return false;
  }
  if (!conjunction ^ left->verify(g, !conjunction ? p : NULL)) return conjunction;
  return right->verify(g, !conjunction ? p : NULL);
}

/**
 * Look for an atom in @a from about the same predicated_real than atom @a p.
 * Fill @a p with its content.
 * @return true when successful.
 */
static bool lookup(property_tree &p, property_tree const &from)
{
  assert(p.atom);
  if (from.left) {
    if (lookup(p, *from.left)) return true;
    return lookup(p, *from.right);
  }
  assert(from.atom);
  if (p.conjunction != from.conjunction) return false;
  if (p.atom->real != from.atom->real) return false;
  if (!is_defined(from.atom->bnd())) return false;
  p.atom->bnd() = from.atom->bnd();
  return true;
}

void property_tree::fill_undefined(property_tree const &base)
{
  if (atom) {
    if (!atom->real.pred_bnd() || is_defined(atom->bnd())) return;
    if (!lookup(*this, base)) clear();
    return;
  }
  assert(left && right);
  left->fill_undefined(base);
  right->fill_undefined(base);
  if (left->empty()) {
    property_tree *p = right;
    right = NULL;
    swap(*p);
    delete p;
  } else if (right->empty()) {
    property_tree *p = left;
    left = NULL;
    swap(*p);
    delete p;
  }
}

void property_tree::get_splitting(splitting &res) const
{
  if (atom) {
    if (!atom->real.pred_bnd()) return;
    interval const &b = atom->bnd();
    if (!is_defined(b)) return;
    split_point_mset &nums = res[atom->real];
    number const &l = lower(b), &u = upper(b);
    if (l == u) return;
    if (l != number::neg_inf) nums.insert(split_point(l, false));
    if (u != number::pos_inf) nums.insert(split_point(u, true));
  } else {
    left->get_splitting(res);
    right->get_splitting(res);
  }
}
