/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#ifndef PROOFS_PROPERTY_HPP
#define PROOFS_PROPERTY_HPP

#include <cassert>
#include <list>
#include <map>
#include <set>
#include <vector>
#include "numbers/interval.hpp"

enum predicate_type
{
  PRED_BND = 0, PRED_ABS, PRED_REL,
  PRED_FIX = 4, PRED_FLT,
  PRED_EQL = 8, PRED_NZR
};

struct ast_real;

class predicated_real
{
  long d1, d2;
 public:
  predicated_real(): d1(0), d2(0) {}
  predicated_real(ast_real const *r, predicate_type p)
    : d1(reinterpret_cast< long >(r) | (p & 3)), d2(p >> 2) {}
  predicated_real(ast_real const *r1, ast_real const *r2, predicate_type p)
    : d1(reinterpret_cast< long >(r1) | (p & 3)), d2(reinterpret_cast< long >(r2) | (p >> 2)) {}
  predicate_type pred() const { return (predicate_type)((d1 & 3) | ((d2 & 3) << 2)); }
  bool pred_bnd() const { return (d2 & 3) == 0; }
  bool pred_cst() const { return (d2 & 3) == 1; }
  ast_real const *real()  const { return reinterpret_cast< ast_real const * >(d1 & ~3); }
  ast_real const *real2() const { return reinterpret_cast< ast_real const * >(d2 & ~3); }
  bool operator==(predicated_real const &r) const { return d1 == r.d1 && d2 == r.d2; }
  bool operator!=(predicated_real const &r) const { return d1 != r.d1 || d2 != r.d2; }
  bool operator< (predicated_real const &r) const { return d1 < r.d1 || (d1 == r.d1 && d2 < r.d2); }
  bool null() const { return d1 == 0; }
};

typedef std::vector< predicated_real > preal_vect;

class property {
  union store_t {
    char _bnd[sizeof(interval)];
    long _int;
  };
  store_t store;
  interval       &_bnd()       { return *reinterpret_cast< interval       * >(&store); }
  interval const &_bnd() const { return *reinterpret_cast< interval const * >(&store); }
 public:
  predicated_real real;
  interval &bnd()
  { assert(real.pred_bnd()); return _bnd(); }
  interval const &bnd() const
  { assert(real.pred_bnd()); return _bnd(); }
  long &cst()
  { assert(real.pred_cst()); return store._int; }
  long const &cst() const
  { assert(real.pred_cst()); return store._int; }
  property();
  property(ast_real const *);
  property(ast_real const *, interval const &);
  property(predicated_real const &);
  property(predicated_real const &, interval const &);
  property(predicated_real const &, long);
  property(property const &);
  property &operator=(property const &);
  ~property();
  bool implies(property const &) const;
  bool strict_implies(property const &) const;
  void intersect(property const &);
  void hull(property const &);
  bool null() const { return real.null(); }
  void clear();
  bool operator<(property const &r) const;
  bool operator==(property const &r) const;
  bool operator!=(property const &r) const { return !(*this == r); }
};

struct property_vect: std::vector< property > {
  bool implies(property_vect const &) const;
  int find_compatible_property(property const &) const;
};

struct node;
struct graph_t;

struct split_point;

typedef std::multiset<split_point> split_point_mset;
typedef std::map<predicated_real, split_point_mset> splitting;

typedef std::map<predicated_real, property> undefined_map;

struct property_tree
{
  bool conjunction;
  property_tree *left, *right;
  property *atom;
  property_tree()
    : conjunction(false), left(NULL), right(NULL), atom(NULL) {}
  property_tree(property const &);
  property_tree(property_tree const &);
  property_tree &operator=(property_tree const &);
  ~property_tree();
  bool operator<(property_tree const &t) const;
  bool operator==(property_tree const &t) const;
  bool operator!=(property_tree const &t) const { return !(*this == t); }
  bool empty() const { return !left && !atom; }

  void clear();
  void swap(property_tree &);

  void negate();

  /**
   * Fills leaves that have an undefined interval with a corresponding
   * interval from @a p. Removes leaves for which no interval can be found.
   */
  void fill_undefined(property_tree const &p);

  /**
   * Simplifies the tree according to property @a p (modality @a positive).
   * @param force If set, the function removes undefined yet matching leaves.
   * @param changed Set to true if a change happened.
   * @param tgt Set to the resulting tree if the result is nonzero.
   * @return zero if the tree is not empty yet, a positive value if it is
   *         true, a negative value if it is false.
   */
  int try_simplify(property const &p, bool positive, undefined_map *force, bool &changed, property_tree &tgt) const;

  int simplify(property const &p);

  /**
   * Checks if the tree is contradicted by graph @a g.
   * @param p Pointer to an optional storage for a remaining property.
   * @return false if the tree has remaining properties.
   */
  bool verify(graph_t *g, property *p) const;

  void get_splitting(splitting &) const;
};

typedef std::list<property_tree> property_trees;

#endif // PROOFS_PROPERTY_HPP
