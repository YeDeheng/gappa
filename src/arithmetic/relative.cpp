/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <climits>
#include <map>
#include <sstream>
#include "parser/ast.hpp"
#include "numbers/interval_arith.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"

extern bool parameter_constrained;

struct relative_function_class: function_class
{
  interval he, hz;
  int prec, min_exp;
  std::string ident;
  relative_function_class(real_op_type, int, int, std::string const &);
  virtual interval round                         (interval const &, std::string &) const;
  virtual interval relative_error                                  (std::string &) const;
  virtual interval relative_error_from_exact_abs (interval const &, std::string &) const;
  virtual interval relative_error_from_approx_abs(interval const &, std::string &) const;
  virtual std::string description() const { return "relative" + ident; }
  virtual std::string pretty_name() const;
};

relative_function_class::relative_function_class(real_op_type t, int p, int e, std::string const &i)
  : function_class(t, TH_RND | (e == INT_MIN ? TH_REL : (TH_REL_EXA_ABS | TH_REL_APX_ABS)))
  , prec(p), min_exp(e), ident(i)
{
  he = from_exponent(-p, 0);
  if (min_exp != INT_MIN) hz = from_exponent(min_exp, 0);
}

interval relative_function_class::round(interval const &i, std::string &name) const {
  name = "rel_round" + ident;
  return i * (interval(number(1), number(1)) + he);
}

interval relative_function_class::relative_error(std::string &name) const
{
  assert(min_exp == INT_MIN);
  name = "rel_error" + ident;
  return he;
}

interval relative_function_class::relative_error_from_exact_abs(interval const &i, std::string &name) const
{
  assert(min_exp != INT_MIN);
  if (parameter_constrained && !is_empty(intersect(i, hz)))
    return interval();
  name = "rel_error" + ident;
  return he;
}

interval relative_function_class::relative_error_from_approx_abs(interval const &i, std::string &name) const
{
  assert(min_exp != INT_MIN);
  if (parameter_constrained && !is_empty(intersect(i, hz)))
    return interval();
  name = "rel_error_inv" + ident;
  return he;
}

std::string relative_function_class::pretty_name() const
{
  std::ostringstream s;
  s << ident.substr(1, 3) << "_rel<" << prec;
  if (min_exp != INT_MIN) s << ',' << min_exp;
  s << '>';
  return s.str();
}

struct relative_function_generator: function_generator
{
  char const *name;
  real_op_type type;
  typedef std::map< long long int, relative_function_class > relative_cache;
  mutable relative_cache cache;
  relative_function_generator(char const *n, real_op_type t)
    : function_generator(n), name(n), type(t) {}
  virtual function_class const *operator()(function_params const &) const;
};

function_class const *relative_function_generator::operator()(function_params const &p) const {
  int prec, min_exp;
  if (p.empty() || !param_int(p[0], prec)) return NULL;
  if (p.size() == 1) min_exp = INT_MIN;
  else if (p.size() != 2 || !param_int(p[1], min_exp)) return NULL;
  long long int h = (((long long int)min_exp) << 32) | prec;
  relative_cache::const_iterator j = cache.find(h);
  if (j != cache.end()) return &j->second;
  std::ostringstream s;
  s << ',' << std::string(name, 3) << ',' << prec;
  if (min_exp != INT_MIN) s << ',' << min_exp;
  j = cache.insert(std::make_pair(h, relative_function_class(type, prec, min_exp, s.str()))).first;
  return &j->second;
}

static relative_function_generator dummy_add("add_rel", BOP_ADD);
static relative_function_generator dummy_sub("sub_rel", BOP_SUB);
static relative_function_generator dummy_mul("mul_rel", BOP_MUL);
static relative_function_generator dummy_fma("fma_rel", COP_FMA);
