/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <algorithm>
#include <cassert>
#include <iostream>
#include <sstream>
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "parser/ast.hpp"
#include "parser/pattern.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/property.hpp"
#include "proofs/rewriting.hpp"

typedef std::set< ast_real const * > real_set;
real_set free_variables;
typedef std::set< predicated_real > preal_set;
preal_set input_reals, output_reals;

interval create_interval(ast_number const *, ast_number const *, bool);
void find_unknown_reals(real_set &, ast_real const *);

extern bool warning_unbound_variable;

void check_approx(ast_real const *real)
{
  real_op const *o = boost::get< real_op const >(real);
  if (!o) return;
  // look for an approx/accurate pair
  if (o->type == UOP_ABS)
    o = boost::get< real_op const >(o->ops[0]);
  ast_real const *r = NULL;
  if (o && o->type == BOP_DIV)
  {
    r = o->ops[1];
    o = boost::get< real_op const >(o->ops[0]);
  }
  if (o && o->type == BOP_SUB && (!r || r == o->ops[1]))
    register_approx(o->ops[0], o->ops[1]);
}

static property generate_property(ast_atom const &p, bool goal)
{
  predicated_real pr(p.real, p.real2, p.type);
  output_reals.insert(pr);
  switch (p.type) {
  case PRED_FIX:
  case PRED_FLT:
    input_reals.insert(pr);
    return property(pr, p.cst);
  case PRED_EQL:
    register_approx(p.real, p.real2);
    check_approx(p.real);
    // no break
  case PRED_NZR:
    input_reals.insert(pr);
    return property(pr);
  case PRED_BND:
  case PRED_ABS:
  case PRED_REL:
    break;
  }

  property r(pr);
  if (p.lower || p.upper)
  {
    input_reals.insert(pr);
    if (p.real2)
      register_approx(p.real, p.real2);
    else
      check_approx(p.real);

    interval &bnd = r.bnd();
    bnd = create_interval(p.lower, p.upper, !goal);
    if (is_empty(bnd))
    {
      std::cerr << "Error: the range of " << dump_real_short(pr)
                << " is an empty interval.\n";
      exit(1);
    }
    if (pr.real2() && lower(bnd) <= number(-1))
    {
      std::cerr << "Error: the range of " << dump_real_short(pr)
                << " contains values smaller or equal to -1.\n";
      exit(1);
    }
  }
  else if (!goal)
  {
    std::cerr << "Error: undefined intervals are restricted to conclusions.\n";
    exit(1);
  }
  return r;
}

static void generate_tree(property_tree &tree, ast_prop const *p, bool positive)
{
  assert(tree.empty());
  switch (p->type) {
  case PROP_ATOM:
    tree.atom = new property(generate_property(*p->atom, positive));
    tree.conjunction = positive;
    break;
  case PROP_IMPL:
  case PROP_AND:
  case PROP_OR:
    tree.left = new property_tree;
    tree.right = new property_tree;
    generate_tree(*tree.left, p->lhs, positive ^ (p->type == PROP_IMPL));
    generate_tree(*tree.right, p->rhs, positive);
    tree.conjunction = !positive ^ (p->type == PROP_AND);
    break;
  case PROP_NOT:
    generate_tree(tree, p->lhs, !positive);
    break;
  }
}

#if 0
static void massage_property_tree(property_tree &tree)
{
  std::vector<property_tree::leaf> new_leaves;

  // for any goal x>=b or x<=b, add the converse inequality as a hypothesis
  for (std::vector<property_tree::leaf>::const_iterator i = tree->leaves.begin(),
       i_end = tree->leaves.end(); i != i_end; ++i)
  {
    property const &p = i->first;
    if (!i->second || p.real.pred() != PRED_BND || !is_defined(p.bnd()) ||
        is_bounded(p.bnd())) continue;
    number l = upper(p.bnd()), u = lower(p.bnd());
    if (l == number::pos_inf) {
      l = number::neg_inf;
      if (!p.real.real2()) {
        real_op const *o = boost::get<real_op const>(p.real.real());
        if (o && o->type == UOP_ABS) l = 0;
      }
    } else {
      u = number::pos_inf;
    }
    new_leaves.push_back(property_tree::leaf(property(p.real, interval(l, u)), false));
  }

  tree->leaves.insert(tree->leaves.end(), new_leaves.begin(), new_leaves.end());
}
#endif

static void delete_prop(ast_prop const *p)
{
  switch (p->type) {
  case PROP_AND:
  case PROP_OR:
  case PROP_IMPL:
    delete_prop(p->rhs);
    // no break
  case PROP_NOT:
    delete_prop(p->lhs);
    break;
  case PROP_ATOM:
    delete p->atom;
  }
  delete p;
}

static void check_unbound()
{
  real_set bound_variables;
  for (preal_set::const_iterator i = input_reals.begin(),
       i_end = input_reals.end(); i != i_end; ++i)
  {
    predicated_real const &r = *i;
    find_unknown_reals(bound_variables, r.real());
    if (r.real2()) find_unknown_reals(bound_variables, r.real2());
  }
  real_set s;
  std::set_difference(free_variables.begin(), free_variables.end(),
                      bound_variables.begin(), bound_variables.end(),
                      std::inserter(s, s.begin()));
  free_variables.swap(s);
  for(real_set::const_iterator i = free_variables.begin(), end = free_variables.end(); i != end; ++i) {
    ast_ident const *n = (*i)->name;
    assert(n);
    std::cerr << "Warning: " << n->name << " is a variable without definition, yet it is unbound.\n";
  }
}

void parse_property_tree(property_tree &tree, ast_prop const *p)
{
  generate_tree(tree, p, true);
  delete_prop(p);
}

extern property_tree context;

void generate_graph(ast_prop const *p)
{
  parse_property_tree(context, p);
  context.negate();
  if (warning_unbound_variable)
    check_unbound();
  free_variables.clear();
}

// 0: no rule, 1: a rule but a missing relation, 2: a rule
int test_rewriting(ast_real const *src, ast_real const *dst, std::string &res)
{
  std::ostringstream info;
  for(rewriting_vect::const_iterator i = rewriting_rules.begin(),
      i_end = rewriting_rules.end(); i != i_end; ++i)
  {
    rewriting_rule const &rw = **i;
    if (rw.src.pred() != PRED_BND) continue;
    ast_real_vect holders;
    if (!match(src, rw.src.real(), holders)) continue;
    bool b = holders.size() >= 2 && (!holders[0] || !holders[1]);
    if (!match(dst, rw.dst.real(), holders, true)) continue;
    for(pattern_excl_vect::const_iterator j = rw.excl.begin(),
        j_end = rw.excl.end(); j != j_end; ++j)
      if (rewrite(j->first, holders) == rewrite(j->second, holders)) goto next_rule;
    if (b) {
      assert(holders[0] && holders[1]);
      link_map::const_iterator k = approximates.find(holders[0]);
      if (k != approximates.end() && k->second.find(holders[1]) != k->second.end())
        goto found_rule;
      info << "  " << dump_real(holders[1]) << " ~ " << dump_real(holders[0]) << '\n';
    } else {
      found_rule:
      info.str(std::string());
      for(pattern_cond_vect::const_iterator j = rw.cond.begin(),
          j_end = rw.cond.end(); j != j_end; ++j) {
        info << "  " << dump_real(rewrite(j->real, holders));
        char const *ops[] = { " < ", " <= ", " > ", " >= ", " != " };
        if (j->type == COND_NZ) info << " != 0 ";
        else info << ops[j->type] << j->value;
        info << '\n';
      }
      res = info.str();
      return 2;
    }
    next_rule: ;
  }
  res = info.str();
  return !res.empty();
}
