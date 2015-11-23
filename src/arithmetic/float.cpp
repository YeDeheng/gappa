/*
   Copyright (C) 2004 - 2013 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <algorithm>
#include <cassert>
#include <map>
#include <sstream>
#include "utils.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "parser/pattern.hpp"
#include "proofs/schemes.hpp"

extern bool parameter_constrained;

struct float_format: gs_rounding {
  int min_exp, prec;
  virtual int shift_val(int exp, int sz) const { return std::max(min_exp - exp, sz - prec); }
  float_format() {}
  float_format(int e, int p): min_exp(e), prec(p) {}
};

typedef std::map< ast_ident const *, float_format > float_formats;
static float_formats formats;

#define REGISTER_FORMAT(name, e, p) \
  formats.insert(std::make_pair(ast_ident::find(#name), float_format(e, p)))

RUN_ONCE(register_formats) {
  REGISTER_FORMAT(ieee_32 ,   -149,  24);
  REGISTER_FORMAT(ieee_64 ,  -1074,  53);
  REGISTER_FORMAT(ieee_128, -16494, 113);
  REGISTER_FORMAT(x86_80  , -16445,  64);
}

struct float_rounding_class: function_class
{
  float_format format;
  direction_type type;
  std::string ident;
  float_rounding_class(float_format const &f, direction_type t, std::string const &i)
    : function_class(UOP_ID, TH_RND | TH_ENF | TH_REL_EXA_ABS | TH_REL_APX_ABS |
        (rnd_symmetric(t) ?  TH_ABS_EXA_ABS | TH_ABS_APX_ABS : TH_ABS_EXA_BND | TH_ABS_APX_BND)),
      format(f), type(t), ident(i) {}
  virtual interval round                         (interval const &, std::string &) const;
  virtual interval enforce                       (interval const &, std::string &) const;
  virtual interval absolute_error_from_exact_bnd (interval const &, std::string &) const;
  virtual interval absolute_error_from_exact_abs (interval const &, std::string &) const;
  virtual interval absolute_error_from_approx_bnd(interval const &, std::string &) const;
  virtual interval absolute_error_from_approx_abs(interval const &, std::string &) const;
  virtual interval relative_error_from_exact_abs (interval const &, std::string &) const;
  virtual interval relative_error_from_approx_abs(interval const &, std::string &) const;
  virtual std::string description() const { return "rounding_float" + ident; }
  virtual std::string pretty_name() const;
};

struct float_rounding_generator: function_generator
{
  float_rounding_generator(): function_generator("float") {}
  virtual function_class const *operator()(function_params const &) const;
};

typedef std::map< long long int, float_rounding_class > float_cache;
static float_cache cache;

function_class const *float_rounding_generator::operator()(function_params const &p) const {
  if (p.empty()) return NULL;
  ast_ident const *nf = param_ident(p[0]);
  int nd;
  float_format f;
  if (nf) {
    if (p.size() != 2) return NULL;
    float_formats::const_iterator i = formats.find(nf);
    if (i == formats.end()) return NULL;
    f = i->second;
    nd = 1;
  } else {
    if (p.size() != 3) return NULL;
    if (!param_int(p[0], f.prec) || !param_int(p[1], f.min_exp)) return NULL;
    nd = 2;
  }
  direction_type d = get_direction(p[nd]);
  if (d == ROUND_ARGL) return NULL;
  long long int h = (((long long int)f.min_exp) << 24) | (f.prec << 8) | (int)d;
  float_cache::const_iterator j = cache.find(h);
  if (j != cache.end()) return &j->second;
  std::ostringstream s;
  s << ',' << direction_names[d] << ',' << f.prec << ',' << f.min_exp;
  j = cache.insert(std::make_pair(h, float_rounding_class(f, d, s.str()))).first;
  return &j->second;
}

static float_rounding_generator dummy;

interval float_rounding_class::enforce(interval const &i, std::string &name) const {
  number a = round_number(lower(i), &format, &float_format::roundUP);
  number b = round_number(upper(i), &format, &float_format::roundDN);
  name = "float_enforce";
  return interval(a, (a <= b) ? b : a);
}

interval float_rounding_class::round(interval const &i, std::string &name) const {
  rounding_fun f = direction_functions[type];
  number a = round_number(lower(i), &format, f);
  number b = round_number(upper(i), &format, f);
  name = std::string("float_round,") + direction_names[type];
  return interval(a, b);
}

static int exponent(number const &n, float_format const &f) {
  mpz_t m;
  int e;
  int s;
  mpz_init(m);
  split_exact(n.data->val, m, e, s);
  if (s == 0) e = f.min_exp;
  else {
    e -= f.prec - mpz_sizeinbase(m, 2);
    if (e < f.min_exp) e = f.min_exp;
  }
  mpz_clear(m);
  return e;
}

static bool influenced(number const &n, int e, int e_infl, int infl) {
  mpfr_t x;
  mpfr_init2(x, 150);
  mpfr_set_ui_2exp(x, 1, e, GMP_RNDN);
  if (infl > 0) {
    mpfr_t y;
    mpfr_init(y);
    mpfr_set_ui_2exp(y, 1, e_infl, GMP_RNDN);
    mpfr_add(x, x, y, GMP_RNDD);
    mpfr_clear(y);
  }
  int cmp = mpfr_cmpabs(n.data->val, x);
  mpfr_clear(x);
  return (infl != 1) ? cmp <= 0 : cmp < 0;
}

interval float_rounding_class::absolute_error_from_exact_bnd(interval const &i, std::string &name) const
{
  // directed rounding only
  number const &v1 = lower(i), &v2 = upper(i);
  int e1 = exponent(v1, format), e2 = exponent(v2, format),
      e0 = std::max(e1, e2);
  int e_err = rnd_to_nearest(type) ? e0 - 1 : e0;
  int e = e0 + format.prec - 1;
  name = "float_absolute";
  if (e0 > format.min_exp &&
      (v1 >= 0 || influenced(v1, e, e_err - 1, rnd_influence_direction(type, true ))) &&
      (v2 <= 0 || influenced(v2, e, e_err - 1, rnd_influence_direction(type, false)))) {
    name += "_wide";
    --e_err;
  }
  name += std::string(1, ',') + direction_names[type];
  return from_exponent(e_err, rnd_global_direction_abs(type, i, false));
}

interval float_rounding_class::absolute_error_from_exact_abs(interval const &i, std::string &name) const
{
  // symmetric rounding only
  number const &v = upper(i);
  int e0 = exponent(v, format);
  int e_err = rnd_to_nearest(type) ? e0 - 1 : e0;
  int e = e0 + format.prec - 1;
  name = "float_absolute";
  if (e0 > format.min_exp &&
      influenced(v, e, e_err - 1, rnd_influence_direction(type, false))) {
    name += "_wide";
    --e_err;
  }
  name += std::string(1, ',') + direction_names[type];
  return from_exponent(e_err, rnd_global_direction_abs(type, i, false));
}

interval float_rounding_class::absolute_error_from_approx_bnd(interval const &i, std::string &name) const
{
  // directed rounding only
  int e1 = exponent(lower(i), format), e2 = exponent(upper(i), format);
  int e_err = std::max(e1, e2);
  name = "float_absolute_inv" + std::string(1, ',') + direction_names[type];
  if (rnd_to_nearest(type)) return from_exponent(e_err - 1, 0);
  return from_exponent(e_err, rnd_global_direction_abs(type, i, true));
}

interval float_rounding_class::absolute_error_from_approx_abs(interval const &i, std::string &name) const
{
  // symmetric rounding only
  int e_err = exponent(upper(i), format);
  name = "float_absolute_inv" + std::string(1, ',') + direction_names[type];
  if (rnd_to_nearest(type)) return from_exponent(e_err - 1, 0);
  return from_exponent(e_err, 0);
}

interval float_rounding_class::relative_error_from_exact_abs(interval const &i, std::string &name) const
{
  bool fail = !is_empty(intersect(i, from_exponent(format.min_exp + format.prec - 1, 0)));
  if (parameter_constrained && fail)
    return interval();
  name = fail ? "$FALSE" : "float_relative" + std::string(1, ',') + direction_names[type];
  if (rnd_to_nearest(type)) return from_exponent(-format.prec, 0);
  return from_exponent(1 - format.prec, rnd_global_direction_rel(type)); // cannot use i since it is ABS
}

interval float_rounding_class::relative_error_from_approx_abs(interval const &i, std::string &name) const
{
  bool fail = !is_empty(intersect(i, from_exponent(format.min_exp + format.prec - 1, 0)));
  if (parameter_constrained && fail)
    return interval();
  name = fail ? "$FALSE" : "float_relative_inv" + std::string(1, ',') + direction_names[type];
  if (rnd_to_nearest(type)) return from_exponent(-format.prec, 0);
  return from_exponent(1 - format.prec, rnd_global_direction_rel(type)); // cannot use i since it is ABS
}

std::string float_rounding_class::pretty_name() const
{
  std::ostringstream s;
  s << "float<" << format.prec << ',' << format.min_exp << ',' << direction_names[type] << '>';
  return s.str();
}

// FIX_OF_FLOAT

REGISTER_SCHEME_BEGIN(fix_of_float);
  long min_exp;
  fix_of_float_scheme(predicated_real const &r, long e)
    : proof_scheme(r, preal_vect(), "fix_of_float"), min_exp(e) {}
REGISTER_SCHEME_END_PREDICATE(fix_of_float);

void fix_of_float_scheme::compute(property const [], property &res, std::string &) const
{
  res.cst() = min_exp;
}

proof_scheme *fix_of_float_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_FIX) return NULL;
  real_op const *r = boost::get< real_op const >(real.real());
  if (!r) return NULL;
  float_rounding_class const *f = dynamic_cast< float_rounding_class const * >(r->fun);
  if (!f) return NULL;
  return new fix_of_float_scheme(real, f->format.min_exp);
}

// FLT_OF_FLOAT

REGISTER_SCHEME_BEGIN(flt_of_float);
  long prec;
  flt_of_float_scheme(predicated_real const &r, long p)
    : proof_scheme(r, preal_vect(), "flt_of_float"), prec(p) {}
REGISTER_SCHEME_END_PREDICATE(flt_of_float);

void flt_of_float_scheme::compute(property const [], property &res, std::string &) const
{
  res.cst() = prec;
}

proof_scheme *flt_of_float_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_FLT) return NULL;
  real_op const *r = boost::get< real_op const >(real.real());
  if (!r) return NULL;
  float_rounding_class const *f = dynamic_cast< float_rounding_class const * >(r->fun);
  if (!f) return NULL;
  return new flt_of_float_scheme(real, f->format.prec);
}

// FLOAT_OF_FIX_FLT

REGISTER_SCHEME_BEGIN(float_of_fix_flt);
  preal_vect needed;
  long min_exp, prec;
  float_of_fix_flt_scheme(predicated_real const &r, preal_vect const &v, long e, long p)
    : proof_scheme(r, v, "float_of_fix_flt"), min_exp(e), prec(p) {}
REGISTER_SCHEME_END_PATTERN(float_of_fix_flt, predicated_real(pattern(0), pattern(1), PRED_EQL));

void float_of_fix_flt_scheme::compute(property const hyps[], property &res, std::string &) const
{
  if (hyps[0].cst() < min_exp || hyps[1].cst() > prec) res.clear();
}

proof_scheme *float_of_fix_flt_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  ast_real const *r = holders[1];
  real_op const *o = boost::get<real_op const>(holders[0]);
  if (!o || !o->fun || o->fun->type != UOP_ID || r != o->ops[0])
    return NULL;
  float_rounding_class const *f = dynamic_cast<float_rounding_class const *>(o->fun);
  if (!f) return NULL;
  preal_vect needed;
  needed.push_back(predicated_real(r, PRED_FIX));
  needed.push_back(predicated_real(r, PRED_FLT));
  return new float_of_fix_flt_scheme(real, needed, f->format.min_exp, f->format.prec);
}

// REL_OF_FIX_FLOAT

REGISTER_SCHEME_BEGIN(rel_of_fix_float);
  long min_exp, prec;
  direction_type type;
  rel_of_fix_float_scheme(predicated_real const &r, long e, long p, direction_type t, char const *n)
    : proof_scheme(r, preal_vect(1, predicated_real(r.real2(), PRED_FIX)), n),
      min_exp(e), prec(p), type(t) {}
REGISTER_SCHEME_END_PREDICATE(rel_of_fix_float);

void rel_of_fix_float_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  if (hyps[0].cst() < min_exp) return;
  res.bnd() = rnd_to_nearest(type) ? from_exponent(-prec, 0)
    : from_exponent(1 - prec, rnd_global_direction_rel(type));
}

proof_scheme *rel_of_fix_float_scheme::factory(predicated_real const &real)
{
  float_rounding_class const *f = dynamic_cast< float_rounding_class const * >(relative_rounding_error(real));
  if (!f) return NULL;
  return new rel_of_fix_float_scheme(real, f->format.min_exp, f->format.prec, f->type,
    ("rel_of_fix_float" + std::string(1, ',') + direction_names[f->type]).c_str());
}

// FIX_FLOAT_OF_FIX

REGISTER_SCHEME_BEGIN(fix_float_of_fix);
  fix_float_of_fix_scheme(predicated_real const &r, predicated_real const &n)
    : proof_scheme(r, preal_vect(1, n), "fix_float_of_fix") {}
REGISTER_SCHEME_END_PREDICATE(fix_float_of_fix);

void fix_float_of_fix_scheme::compute(property const hyps[], property &res, std::string &) const
{
  res.cst() = hyps[0].cst();
}

proof_scheme *fix_float_of_fix_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_FIX) return NULL;
  real_op const *r = boost::get< real_op const >(real.real());
  if (!r) return NULL;
  float_rounding_class const *f = dynamic_cast< float_rounding_class const * >(r->fun);
  if (!f) return NULL;
  return new fix_float_of_fix_scheme(real, predicated_real(r->ops[0], PRED_FIX));
}

// FLT_FLOAT_OF_FLT

REGISTER_SCHEME_BEGIN(flt_float_of_flt);
  flt_float_of_flt_scheme(predicated_real const &r, predicated_real const &n)
    : proof_scheme(r, preal_vect(1, n), "flt_float_of_flt") {}
REGISTER_SCHEME_END_PREDICATE(flt_float_of_flt);

void flt_float_of_flt_scheme::compute(property const hyps[], property &res, std::string &) const
{
  res.cst() = hyps[0].cst();
}

proof_scheme *flt_float_of_flt_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_FLT) return NULL;
  real_op const *r = boost::get< real_op const >(real.real());
  if (!r) return NULL;
  float_rounding_class const *f = dynamic_cast< float_rounding_class const * >(r->fun);
  if (!f) return NULL;
  return new flt_float_of_flt_scheme(real, predicated_real(r->ops[0], PRED_FLT));
}
