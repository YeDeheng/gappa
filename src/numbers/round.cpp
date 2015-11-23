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
#include <map>
#include "utils.hpp"
#include "numbers/interval.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"

void split_exact(mpfr_t const &f, mpz_t &frac, int &exp, int &sign) {
  sign = mpfr_sgn(f);
  if (sign == 0) return;
  exp = mpfr_get_z_exp(frac, f);
  mpz_abs(frac, frac); // avoid an MPFR bug
  int d = mpz_scan1(frac, 0);
  if (d > 0) mpz_fdiv_q_2exp(frac, frac, d);
  exp += d;
}

void rnd::shr(int d) {
  assert(d >= 0);
  if (d == 0) return;
  e += d;
  if (!(g || s || d == 1))
    s = !mpz_divisible_2exp_p(m, d - 1);
  else s |= g;
  g = mpz_tstbit(m, d - 1);
  mpz_tdiv_q_2exp(m, m, d);
}

// The lower bit of the mantissa is not necessarily the ulp bit. But testing
// for it in conjunction with the guard bit or the sticky bit works. Otherwise
// the number was not truncated and it does not have to be changed.

bool gs_rounding::rndAW(rnd const &r) const {
  return r.g || r.s;
}

bool gs_rounding::rndNE(rnd const &r) const {
  return r.g && (r.s || mpz_tstbit(r.m, 0));
}

bool gs_rounding::rndNO(rnd const &r) const {
  return r.g && (r.s || !mpz_tstbit(r.m, 0));
}

bool gs_rounding::rndNZ(rnd const &r) const {
  return r.g && r.s;
}

bool gs_rounding::rndNA(rnd const &r) const {
  return r.g;
}

bool gs_rounding::rndOD(rnd const &r) const {
  return (r.g || r.s) && !mpz_tstbit(r.m, 0);
}

void gs_rounding::succ(mpz_t &m, int &e) const {
  assert(mpz_sgn(m) >= 0);
  int dec = shift_val(e, mpz_sizeinbase(m, 2));
  assert(dec >= 0);
  if (dec > 0) {
    mpz_mul_2exp(m, m, dec);
    e -= dec;
  }
  mpz_add_ui(m, m, 1);
  dec = mpz_scan1(m, 0);
  if (dec > 0) mpz_fdiv_q_2exp(m, m, dec);
  e += dec;
}

void gs_rounding::trunc(mpfr_t const &f, rnd &r, int &sign) const {
  r.s = r.g = false;
  split_exact(f, r.m, r.e, sign);
  if (sign == 0) return;
  int dec = shift_val(r.e, mpz_sizeinbase(r.m, 2));
  if (dec <= 0) return;
  r.shr(dec);
}

void gs_rounding::round(mpfr_t &f, rnd_fun g_neg, rnd_fun g_pos) const {
  rnd r;
  int s;
  trunc(f, r, s);
  if (s == 0) return;
  if ((this->*(s > 0 ? g_pos : g_neg))(r)) succ(r.m, r.e);
  mpfr_set_prec(f, std::max<int>(mpz_sizeinbase(r.m, 2), 2));
  int v = mpfr_set_z(f, r.m, GMP_RNDN);
  assert(v == 0);
  mpfr_mul_2si(f, f, r.e, GMP_RNDN);
  if (s < 0) mpfr_neg(f, f, GMP_RNDN);
}

number round_number(number const &f, gs_rounding const *t, rounding_fun r) {
  if (!t) return f;
  number res = f;
  number_base *d = res.unique();
  (t->*r)(d->val);
  return res;
}

typedef std::map< ast_ident const *, direction_type > rounding_directions;
static rounding_directions directions;
rounding_fun direction_functions[nb_directions];
char const *direction_names[nb_directions];

#define REGISTER_DIRECTION(name, type) \
  directions.insert(std::make_pair(ast_ident::find(#name), ROUND_##type)); \
  direction_functions[ROUND_##type] = &gs_rounding::round##type; \
  direction_names[ROUND_##type] = #name

RUN_ONCE(register_directions) {
  REGISTER_DIRECTION(up, UP);
  REGISTER_DIRECTION(dn, DN);
  REGISTER_DIRECTION(zr, ZR);
  REGISTER_DIRECTION(aw, AW);
  REGISTER_DIRECTION(od, OD);
  REGISTER_DIRECTION(ne, NE);
  REGISTER_DIRECTION(no, NO);
  REGISTER_DIRECTION(nz, NZ);
  REGISTER_DIRECTION(na, NA);
  REGISTER_DIRECTION(nu, NU);
  REGISTER_DIRECTION(nd, ND);
}

direction_type get_direction(unsigned long u) {
  rounding_directions::const_iterator i = directions.find(param_ident(u));
  if (i == directions.end()) return ROUND_ARGL;
  return i->second;
}

int rnd_global_direction_abs(direction_type type) {
  if (type == ROUND_DN) return -1;
  if (type == ROUND_UP) return +1;
  return 0;
}

int rnd_global_direction_rel(direction_type type) {
  if (type == ROUND_ZR) return -1;
  if (type == ROUND_AW) return +1;
  return 0;
}

int rnd_global_direction_abs(direction_type type, interval const &i, bool inv)
{
  int sgn = inv ? sign_strict(i) : sign(i);
  if (type == ROUND_DN || (type == ROUND_ZR && sgn > 0) || (type == ROUND_AW && sgn < 0)) return -1;
  if (type == ROUND_UP || (type == ROUND_ZR && sgn < 0) || (type == ROUND_AW && sgn > 0)) return +1;
  return 0;
}

int rnd_global_direction_rel(direction_type type, interval const &i, bool inv)
{
  int sgn = inv ? sign_strict(i) : sign(i);
  if (type == ROUND_ZR || (type == ROUND_DN && sgn > 0) || (type == ROUND_UP && sgn < 0)) return -1;
  if (type == ROUND_AW || (type == ROUND_DN && sgn < 0) || (type == ROUND_UP && sgn > 0)) return +1;
  return 0;
}

// 0: not influenced, 1: influenced except midpoint, 2: influenced
int rnd_influence_direction(direction_type type, bool neg) {
  switch (type) {
  case ROUND_AW:
  case ROUND_OD: return 0;
  case ROUND_ZR:
  case ROUND_NE:
  case ROUND_NZ: return 2;
  case ROUND_NO:
  case ROUND_NA: return 1;
  case ROUND_NU: return neg ? 2 : 1;
  case ROUND_ND: return neg ? 1 : 2;
  case ROUND_UP: return neg ? 1 : 0;
  case ROUND_DN: return neg ? 0 : 1;
  case ROUND_ARGL: assert(false);
  }
  return -1;
}

bool rnd_symmetric(direction_type type) {
  switch (type) {
  case ROUND_AW:
  case ROUND_OD:
  case ROUND_ZR:
  case ROUND_NE:
  case ROUND_NZ:
  case ROUND_NO:
  case ROUND_NA: return true;
  case ROUND_NU:
  case ROUND_ND:
  case ROUND_UP:
  case ROUND_DN: return false;
  case ROUND_ARGL: assert(false);
  }
  return false;
}

/**
 * Simplifies the floating-point number @a f
 * \li toward infinity if @a dir is positive,
 * \li toward zero otherwise.
 *
 * @pre @a f is not zero.
 * @note @a f stays in the same interval (-inf,-1], [-1,0), (0,1], or [1,+inf)
 */
static void simplify(mpfr_t &f, int dir)
{
  mpz_t m;
  int e, s;
  mpz_init(m);
  split_exact(f, m, e, s);
  assert(s != 0);
  if (mpz_cmp_ui(m, 1) == 0)
  {
    // mantissa is 1, so converge toward 1 if allowed
    if (e < 0 && dir > 0) ++e;
    else if (e > 0 && dir < 0) --e;
  }
  else
  {
    // mantissa is odd and bigger than one, so replace the last digit by 0
    (dir < 0 ? mpz_sub_ui : mpz_add_ui)(m, m, 1);
    int d = mpz_scan1(m, 0);
    assert(d > 0);
    mpz_fdiv_q_2exp(m, m, d);
    e += d;
  }
  // mpfr needs two bits at least
  mpfr_set_prec(f, std::max<int>(mpz_sizeinbase(m, 2), 2));
  if (s < 0) mpz_neg(m, m);
  int v = mpfr_set_z(f, m, GMP_RNDN);
  assert(v == 0);
  mpfr_mul_2si(f, f, e, GMP_RNDN);
  mpz_clear(m);
}

/**
 * Simplifies @a f until its mantissa has only one digit.
 * @see ::simplify(mpfr_t &, int)
 */
static void simplify_full(mpfr_t &f, int dir)
{
  mpz_t m;
  int e, s;
  mpz_init(m);
  split_exact(f, m, e, s);
  assert(s != 0);
  int d = mpz_sizeinbase(m, 2);
  if (dir < 0) --d;
  e += d;
  mpfr_set_prec(f, 2);
  mpfr_set_si(f, s < 0 ? -1 : 1, GMP_RNDN);
  mpfr_mul_2si(f, f, e, GMP_RNDN);
  mpz_clear(m);
}

/**
 * Simplifies @a f toward the infinity with the same sign than @a dir.
 * @see ::simplify(mpfr_t &, int)
 */
number simplify(number const &f, int dir)
{
  number res = f;
  if (f == 0) return res;
  number_base *d = res.unique();
  simplify(d->val, f < 0 ? -dir : dir);
  return res;
}

/**
 * Simplifies @a f toward the infinity with the same sign than @a dir until its mantissa has only one digit.
 * @see ::simplify_full(mpfr_t &, int)
 */
number simplify_full(number const &f, int dir)
{
  number res = f;
  if (f == 0) return res;
  number_base *d = res.unique();
  simplify_full(d->val, f < 0 ? -dir : dir);
  return res;
}
