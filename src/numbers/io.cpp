/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <sstream>
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"

static number read_number(ast_number const &n, mp_rnd_t rnd) {
  number_base *res = new number_base;
  switch (n.base) {
  case 10: {
    std::stringstream s;
    s << n.mantissa << 'e' << n.exponent;
    mpfr_set_str(res->val, s.str().c_str(), 10, rnd);
    break; }
  case 2: {
    mpfr_set_str(res->val, n.mantissa.c_str(), 10, rnd);
    mpfr_mul_2si(res->val, res->val, n.exponent, rnd);
    break; }
  case 1: {
    mpfr_set_str(res->val, n.mantissa.c_str(), 10, rnd);
    break; }
  case 0: {
    mpfr_set_ui(res->val, 0, rnd);
    break; }
  default:
    assert(false);
  }
  return res;
}

interval create_interval(ast_number const *lower, ast_number const *upper, bool widen) {
  mp_rnd_t d1 = widen ? GMP_RNDD : GMP_RNDU;
  mp_rnd_t d2 = widen ? GMP_RNDU : GMP_RNDD;
  return interval(lower ? read_number(*lower, d1) : number::neg_inf,
                  upper ? read_number(*upper, d2) : number::pos_inf);
}

static std::string signed_lexical(mpz_t const &frac, bool sgn) {
  std::string res;
  if (sgn) res = '-';
  char *s = mpz_get_str(NULL, 10, frac);
  res += s;
  free(s);
  return res;
}

static std::string get_real_split(mpfr_t const &f, int &exp, bool &zero, bool beautify)
{
  mpz_t frac;
  mpz_init(frac);
  int sgn;
  split_exact(f, frac, exp, sgn);
  zero = sgn == 0;
  if (zero) {
    mpz_clear(frac);
    return "0";
  }
  if (beautify && exp > 0 && exp + mpz_sizeinbase(frac, 2) < 20) {
    mpz_mul_2exp(frac, frac, exp);
    exp = 0;
  }
  std::string res = signed_lexical(frac, sgn < 0);
  mpz_clear(frac);
  return res;
}

std::string get_real_split(number const &f, int &exp, bool &zero, bool beautify)
{
  return get_real_split(f.data->val, exp, zero, beautify);
}

io_format change_io_format::current = IO_APPROX;

static std::string mpfr_approx(mpfr_t const &f)
{
  char buf[20];
  mpfr_snprintf(buf, 20, "%Rg", f);
  return buf;
}

std::ostream &operator<<(std::ostream &stream, number const &value)
{
  mpfr_t const &f = value.data->val;
  if (change_io_format::current == IO_APPROX || mpfr_inf_p(f)) {
    stream << mpfr_approx(f);
    return stream;
  }
  bool zero; int exp;
  std::string s = get_real_split(f, exp, zero, true);
  bool neg = s[0] == '-';
  stream << s;
  if (!zero && exp != 0) stream << 'b' << exp;
  else if (s.size() < 5U + neg) return stream;
  if (change_io_format::current == IO_EXACT) return stream;
  stream << " {" << mpfr_approx(f) << ", ";
  if (neg) stream << '-';
  mpfr_t g;
  mpfr_init2(g, 20);
  mpfr_abs(g, f, GMP_RNDN);
  mpfr_log2(g, g, GMP_RNDN);
  stream << "2^(" << mpfr_approx(g) << ")}";
  mpfr_clear(g);
  return stream;
}

std::ostream &operator<<(std::ostream &stream, interval const &u)
{
  if (is_defined(u)) stream << '[' << lower(u) << ", " << upper(u) << ']';
  else stream << '?';
  return stream;
}
