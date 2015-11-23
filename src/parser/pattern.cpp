/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <set>
#include <boost/utility/enable_if.hpp>
#include <boost/type_traits/is_same.hpp>
#include <boost/variant.hpp>
#include "parser/pattern.hpp"

struct match_visitor: boost::static_visitor< bool >
{
  bool visit(ast_real const *src, ast_real const *dst) const;
  template< typename T, typename U > bool operator()(T const &, U const &) const { return false; }
  template< typename T > bool operator()(T const &r1, T const &r2) const { return r1 == r2; }
  bool operator()(real_op const &r1, real_op const &r2) const;
  ast_real_vect &holders;
  bool transparent;
  match_visitor(ast_real_vect &h, bool b): holders(h), transparent(b) {}
};

bool match_visitor::operator()(real_op const &r1, real_op const &r2) const {
  if (r1.type != r2.type || r1.fun != r2.fun) return false;
  unsigned s = r1.ops.size();
  if (s != r2.ops.size()) return false;
  for(unsigned i = 0; i < s; ++i)
    if (!visit(r1.ops[i], r2.ops[i])) return false;
  return true;
}

bool match_visitor::visit(ast_real const *src, ast_real const *dst) const
{
  if (src == dst) return true;
  if (hidden_real const *h = boost::get< hidden_real const >(dst))
    return transparent ? visit(src, h->real) : false;
  if (!dst->has_placeholder) return false;
  placeholder const *p = boost::get< placeholder const >(dst);
  if (!p) return boost::apply_visitor(*this, *src, *dst);
  unsigned i = p->num;
  if (p->num == -1) {
    // -1 is used to force two holders when only pattern(0) is present
    i = 0;
    if (holders.size() < 2) holders.resize(2, NULL);
  } else if (i >= holders.size()) holders.resize(i + 1, NULL);
  ast_real const *&r1 = holders[i];
  if (!r1) r1 = src;
  else if (r1 != src) return false;
  return true;
}

bool match(ast_real const *src, ast_real const *dst, ast_real_vect &holders, bool transparent)
{
  return match_visitor(holders, transparent).visit(src, dst);
}

struct rewrite_visitor: boost::static_visitor< ast_real const * > {
  ast_real const *visit(ast_real const *dst) const;
  template< typename T > ast_real const *operator()(T const &r) const { return normalize(ast_real(r)); }
  ast_real const *operator()(undefined_real const &) const { assert(false); }
  ast_real const *operator()(real_op const &r) const;
  ast_real const *operator()(placeholder const &i) const;
  ast_real const *operator()(hidden_real const &h) const;
  ast_real_vect const &holders;
  rewrite_visitor(ast_real_vect const &h): holders(h) {}
};

ast_real const *rewrite_visitor::operator()(placeholder const &i) const
{
  unsigned j = i.num == -1 ? 0 : i.num;
  assert(j < holders.size());
  ast_real const *r = holders[j];
  assert(r);
  return r;
}

ast_real const *rewrite_visitor::operator()(hidden_real const &h) const
{
  return normalize(hidden_real(visit(h.real)));
}

ast_real const *rewrite_visitor::operator()(real_op const &r) const {
  ast_real_vect ops;
  unsigned s = r.ops.size();
  ops.reserve(s);
  for(unsigned i = 0; i < s; ++i)
    ops.push_back(visit(r.ops[i]));
  return normalize(ast_real(real_op(r.type, r.fun, ops)));
}

ast_real const *rewrite_visitor::visit(ast_real const *dst) const
{
  if (!dst->has_placeholder) return dst;
  return boost::apply_visitor(*this, *dst);
}

ast_real const *rewrite(ast_real const *dst, ast_real_vect const &holders) {
  return rewrite_visitor(holders).visit(dst);
}

struct unhide_visitor: boost::static_visitor< ast_real const * >
{
  ast_real const *visit(ast_real const *dst) const;
  template< typename T > ast_real const *operator()(T const &r) const { return normalize(ast_real(r)); }
  ast_real const *operator()(undefined_real const &) const { assert(false); }
  ast_real const *operator()(real_op const &r) const;
  ast_real const *operator()(hidden_real const &h) const { return visit(h.real); }
};

ast_real const *unhide_visitor::operator()(real_op const &r) const
{
  ast_real_vect ops;
  unsigned s = r.ops.size();
  ops.reserve(s);
  for(unsigned i = 0; i < s; ++i)
    ops.push_back(visit(r.ops[i]));
  return normalize(ast_real(real_op(r.type, r.fun, ops)));
}

ast_real const *unhide_visitor::visit(ast_real const *dst) const
{
  if (!dst->has_placeholder) return dst;
  return boost::apply_visitor(*this, *dst);
}

ast_real const *unhide(ast_real const *dst)
{
  return unhide_visitor().visit(dst);
}

struct missing_visitor: boost::static_visitor<void>
{
  void visit(ast_real const *dst);
  template<typename T> void operator()(T const &) {}
  void operator()(undefined_real const &) { assert(false); }
  void operator()(real_op const &r);
  void operator()(placeholder const &i);
  void operator()(hidden_real const &h) { visit(h.real); }
  int last;
  missing_visitor(): last(-1) {}
};

void missing_visitor::operator()(placeholder const &i)
{
  int j = i.num == -1 ? 1 : i.num;
  if (j >= last) last = j;
}

void missing_visitor::operator()(real_op const &r)
{
  for (unsigned i = 0; i < r.ops.size(); ++i) visit(r.ops[i]);
}

void missing_visitor::visit(ast_real const *dst)
{
  if (dst->has_placeholder) boost::apply_visitor(*this, *dst);
}

int count_missing(ast_real const *r)
{
  missing_visitor mv;
  mv.visit(r);
  return mv.last + 1;
}

typedef std::set< ast_real const * > real_set;

struct unknown_visitor: boost::static_visitor< void > {
  void visit(ast_real const *) const;
  template< typename T > void operator()(T const &) const { return; }
  void operator()(real_op const &) const;
  real_set &reals;
  unknown_visitor(real_set &r): reals(r) {}
};

void unknown_visitor::operator()(real_op const &r) const {
  for(ast_real_vect::const_iterator i = r.ops.begin(), end = r.ops.end(); i != end; ++i)
    visit(*i);
}

void unknown_visitor::visit(ast_real const *dst) const {
  if (boost::get< undefined_real const >(dst)) reals.insert(dst);
  return boost::apply_visitor(*this, *dst);
}

void find_unknown_reals(real_set &s, ast_real const *r) {
  unknown_visitor(s).visit(r);
}

#define PATTERN_OP(symb, op) \
  pattern pattern::operator symb(pattern const &p) const \
  { return pattern(real_op(real, BOP_##op, p.real)); }
PATTERN_OP(+, ADD)
PATTERN_OP(-, SUB)
PATTERN_OP(*, MUL)
PATTERN_OP(/, DIV)

#define PATTERN_COND(symb, op)	\
  pattern_cond pattern::operator symb(int v) const { \
    pattern_cond res;		\
    res.real = real;		\
    res.value = v;		\
    res.type = COND_##op;	\
    return res;			\
  }
PATTERN_COND(<, LT)
PATTERN_COND(>, GT)
PATTERN_COND(<=, LE)
PATTERN_COND(>=, GE)
PATTERN_COND(!=, NE)

pattern pattern::operator-() const	{ return pattern(real_op(UOP_NEG, real)); }
pattern pattern::abs(pattern const &p)	{ return pattern(real_op(UOP_ABS, p.real)); }
pattern pattern::sqrt(pattern const &p)	{ return pattern(real_op(UOP_SQRT, p.real)); }
pattern pattern::log(pattern const &p)	{ return pattern(real_op(UOP_LOG, p.real)); }
pattern pattern::exp(pattern const &p)	{ return pattern(real_op(UOP_EXP, p.real)); }
pattern pattern::log2(pattern const &p)	{ return pattern(real_op(UOP_LOG2, p.real)); }
pattern pattern::exp2(pattern const &p)	{ return pattern(real_op(UOP_EXP2, p.real)); }
pattern pattern::hide(pattern const &p)	{ return pattern(hidden_real(p.real)); }

pattern_cond pattern::operator~() const {
  pattern_cond res;
  res.real = real;
  res.value = 0;
  res.type = COND_NZ;
  return res;
}

bool relative_error(ast_real const *src, ast_real const *dst[2])
{
  real_op const *p = boost::get< real_op const >(src);
  if (!p || p->type != BOP_DIV) return false;
  real_op const *o = boost::get< real_op const >(p->ops[0]);
  if (!o || o->type != BOP_SUB || o->ops[1] != p->ops[1]) return false;
  dst[0] = p->ops[1];
  dst[1] = o->ops[0];
  return true;
}

function_class const *absolute_rounding_error(ast_real const *src, ast_real const *dst[2]) {
  real_op const *p = boost::get< real_op const >(src);
  if (!p || p->type != BOP_SUB) return NULL;
  dst[0] = p->ops[1];
  dst[1] = p->ops[0];
  real_op const *o = boost::get< real_op const >(dst[1]);
  if (!o || !o->fun) return NULL;
  return (dst[0] != unround(o->fun->type, o->ops)) ? NULL : o->fun;
}

function_class const *relative_rounding_error(predicated_real const &src) {
  if (src.pred() != PRED_REL) return NULL;
  real_op const *o = boost::get< real_op const >(src.real());
  if (!o || !o->fun) return NULL;
  return (src.real2() != unround(o->fun->type, o->ops)) ? NULL : o->fun;
}
