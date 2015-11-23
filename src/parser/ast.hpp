/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#ifndef PARSER_AST_HPP
#define PARSER_AST_HPP

#include <string>
#include <vector>
#include "parser/ast_real.hpp"
#include "proofs/property.hpp"

struct ast_atom
{
  predicate_type type;
  ast_real const *real, *real2;
  ast_number const *lower, *upper;
  long cst;
  ast_atom(predicate_type t, ast_real const *r1, ast_real const *r2,
    ast_number const *l, ast_number const *u, long c)
  : type(t), real(r1), real2(r2), lower(l), upper(u), cst(c) {}
};

inline ast_atom *ast_atom_bnd(ast_real const *r, ast_number const *l, ast_number const *u)
{ return new ast_atom(PRED_BND, r, NULL, l, u, 0); }

inline ast_atom *ast_atom_rel(ast_real const *r1, ast_real const *r2, ast_number const *l, ast_number const *u)
{ return new ast_atom(PRED_REL, r1, r2, l, u, 0); }

inline ast_atom *ast_atom_fix(ast_real const *r, long c)
{ return new ast_atom(PRED_FIX, r, NULL, NULL, NULL, c); }

inline ast_atom *ast_atom_flt(ast_real const *r, long c)
{ return new ast_atom(PRED_FLT, r, NULL, NULL, NULL, c); }

inline ast_atom *ast_atom_eql(ast_real const *r1, ast_real const *r2)
{ return new ast_atom(PRED_EQL, r1, r2, NULL, NULL, 0); }

inline ast_atom *ast_atom_nzr(ast_real const *r)
{ return new ast_atom(PRED_NZR, r, NULL, NULL, NULL, 0); }

enum ast_prop_type { PROP_ATOM, PROP_NOT, PROP_AND, PROP_OR, PROP_IMPL };

struct ast_prop {
  ast_prop_type type;
  ast_prop const *lhs, *rhs;
  ast_atom const *atom;
  ast_prop(ast_atom const *a): type(PROP_ATOM), atom(a) {}
  ast_prop(ast_prop const *p): type(PROP_NOT), lhs(p) {}
  ast_prop(ast_prop const *l, ast_prop_type t, ast_prop const *r): type(t), lhs(l), rhs(r) {}
};

typedef std::vector< ast_prop const * > ast_prop_vect;

struct hint_cond
{
  condition_type type;
  ast_real const *real;
  ast_number const *value;
  hint_cond(condition_type t, ast_real const *r, ast_number const *v)
    : type(t), real(r), value(v) {}
};

typedef std::vector< hint_cond const * > hint_cond_vect;

typedef std::vector< unsigned long > function_params;

struct function_generator {
  function_generator(bool) {}
  function_generator(const char *);
  virtual function_class const *operator()(function_params const &) const = 0;
  virtual ~function_generator() {}
};

struct default_function_generator: function_generator {
  function_class const *fun;
  default_function_generator(function_class const *f): function_generator(false), fun(f) {}
  default_function_generator(const char *s, function_class const *f): function_generator(s), fun(f) {}
  virtual function_class const *operator()(function_params const &) const;
};

enum ident_type { ID_NONE, ID_VAR, ID_FUN };

struct ast_ident {
  std::string name;
  ident_type type;
  union {
    function_generator const *fun;
    ast_real const *var;
  };
  ast_ident(std::string const &s): name(s), type(ID_NONE) {}
  bool operator<(ast_ident const &i) const { return name < i.name; }
  static ast_ident *find(std::string const &s);
  static ast_ident *temp();
};

std::string dump_real(ast_real const *, unsigned = 0);
struct predicated_real;
std::string dump_real(predicated_real const &);
std::string dump_real_short(predicated_real const &);
struct property;
std::string dump_property(property const &);
std::string dump_property_nice(property const &);

inline ast_ident const *param_ident(unsigned long l) {
  return (l & 1) ? NULL : reinterpret_cast< ast_ident const * >(l);
}

inline bool param_int(unsigned long l, int &i) {
  i = static_cast< long >(l) >> 1;
  return (l & 1);
}

#endif // PARSER_AST_HPP
