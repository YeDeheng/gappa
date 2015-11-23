/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#ifndef PARSER_AST_REAL_HPP
#define PARSER_AST_REAL_HPP

#include <map>
#include <set>
#include <string>
#include <vector>
#include <boost/blank.hpp>
#include <boost/variant/get.hpp>
#include <boost/variant/variant.hpp>

struct ast_number {
  std::string mantissa;
  int exponent;
  int base;
  bool operator<(ast_number const &v) const
  { return base < v.base || (base == v.base && (exponent < v.exponent || (exponent == v.exponent && mantissa < v.mantissa))); }
};

ast_number *normalize(ast_number const &);

extern ast_number const *token_zero, *token_one;

enum condition_type { COND_LT, COND_LE, COND_GT, COND_GE, COND_NE, COND_NZ };

enum real_op_type { UOP_ID, UOP_NEG, UOP_SQRT, UOP_ABS, UOP_EXP, UOP_LOG, UOP_EXP2, UOP_LOG2, BOP_ADD, BOP_SUB, BOP_MUL, BOP_DIV, COP_FMA, ROP_FUN, ROP_UNK };

struct interval;

struct function_class {
  real_op_type type;
  int theorem_mask;
  static const int
    TH_RND = 1, TH_ENF = 2, TH_ABS = 4, TH_REL = 8,
    TH_ABS_EXA_BND = 16,  TH_ABS_EXA_ABS = 32,  TH_ABS_APX_BND = 64,   TH_ABS_APX_ABS = 128,
    TH_REL_EXA_BND = 256, TH_REL_EXA_ABS = 512, TH_REL_APX_BND = 1024, TH_REL_APX_ABS = 2048;
  function_class(real_op_type t, int m): type(t), theorem_mask(m) {}
  virtual interval round                         (interval const &, std::string &) const;
  virtual interval enforce                       (interval const &, std::string &) const;
  virtual interval absolute_error                                  (std::string &) const;
  virtual interval relative_error                                  (std::string &) const;
  virtual interval absolute_error_from_exact_bnd (interval const &, std::string &) const;
  virtual interval absolute_error_from_exact_abs (interval const &, std::string &) const;
  virtual interval absolute_error_from_approx_bnd(interval const &, std::string &) const;
  virtual interval absolute_error_from_approx_abs(interval const &, std::string &) const;
  virtual interval relative_error_from_exact_bnd (interval const &, std::string &) const;
  virtual interval relative_error_from_exact_abs (interval const &, std::string &) const;
  virtual interval relative_error_from_approx_bnd(interval const &, std::string &) const;
  virtual interval relative_error_from_approx_abs(interval const &, std::string &) const;
  virtual std::string description() const = 0;
  virtual std::string pretty_name() const = 0;
  virtual ~function_class() {}
};

struct ast_real;

typedef std::vector< ast_real const * > ast_real_vect;
typedef std::set < ast_real const * > ast_real_set;

struct real_op {
  ast_real_vect ops;
  function_class const *fun;
  real_op_type type;
  real_op(real_op_type t, ast_real_vect const &o): ops(o), fun(NULL), type(t) {}
  real_op(real_op_type t, function_class const *f, ast_real_vect const &o): ops(o), fun(f), type(t) {}
  real_op(function_class const *f, ast_real_vect const &o): ops(o), fun(f), type(ROP_FUN) {}
  real_op(function_class const *f, ast_real const *o): ops(1, o), fun(f), type(ROP_FUN) {}
  real_op(real_op_type t, ast_real const *o): ops(1, o), fun(NULL), type(t) {}
  real_op(ast_real const *l, real_op_type t, ast_real const *r): fun(NULL), type(t) { ops.push_back(l); ops.push_back(r); }
  bool operator==(real_op const &v) const;
  bool operator<(real_op const &v) const;
};

struct ast_ident;

struct placeholder
{
  int num;
  placeholder(int n): num(n) {}
  bool operator==(placeholder const &v) const { return num == v.num; }
  bool operator< (placeholder const &v) const { return num <  v.num; }
};

struct hidden_real
{
  ast_real const *real;
  hidden_real(ast_real const *r): real(r) {}
  bool operator==(hidden_real const &v) const { return real == v.real; }
  bool operator< (hidden_real const &v) const { return real <  v.real; }
};

typedef boost::blank undefined_real;

typedef boost::variant
  < undefined_real
  , ast_number const *
  , hidden_real
  , real_op
  , placeholder
  > ast_real_aux;

extern void set_flags(ast_real *r, real_op const *p);

struct ast_real: ast_real_aux
{
  mutable ast_ident const *name;
  bool is_constant, has_placeholder;
  ast_real(ast_ident const *v)
    : ast_real_aux(undefined_real()), name(v), is_constant(false), has_placeholder(false) {}
  ast_real(ast_number const *v)
    : ast_real_aux(v), name(NULL), is_constant(true), has_placeholder(false) {}
  ast_real(hidden_real const &v)
    : ast_real_aux(v), name(NULL), is_constant(false), has_placeholder(v.real->has_placeholder) {}
  ast_real(real_op const &v)
    : ast_real_aux(v), name(NULL) { set_flags(this, &v); }
  ast_real(placeholder const &v)
    : ast_real_aux(v), name(NULL), is_constant(false), has_placeholder(true) {}
  bool operator==(ast_real const &v) const;
  bool operator<(ast_real const &v) const;
};

inline bool is_constant(ast_real const *r) { return r->is_constant; }
ast_real *normalize(ast_real const &);
ast_real const *unround(real_op_type, ast_real_vect const &);

typedef std::map< ast_real const *, ast_real_set > link_map;
extern link_map accurates, approximates;
bool register_approx(ast_real const *r1, ast_real const *r2);

#endif // PARSER_AST_REAL_HPP
