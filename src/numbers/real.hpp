/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#ifndef NUMBERS_REAL_HPP
#define NUMBERS_REAL_HPP

#include <gmp.h>
#include <mpfr.h>

struct ref_counter_t {
  int nb;
  ref_counter_t(): nb(1) {}
  void incr() { ++nb; }
  bool decr() { return --nb == 0; }
};

extern int parameter_internal_precision;

struct number_base {
  mutable ref_counter_t ref_counter;
  mpfr_t val;
  number_base() { mpfr_init2(val, parameter_internal_precision); }
  ~number_base() { mpfr_clear(val); }
  number_base const *clone() const { ref_counter.incr(); return this; }
  void destroy() const { if (ref_counter.decr()) delete this; }
};

extern number_base *empty_mpfr;

struct number {
  mutable number_base const *data;
  mpfr_t const &mpfr_data() const { return data->val; }

  number(): data(empty_mpfr->clone()) {}
  number(int);
  number(double);
  number(number_base const *d): data(d) {}
  number(number const &v): data(v.data->clone()) {}
  number &operator=(number const &v);
  ~number() { data->destroy(); }
  number_base *unique() const;
  bool operator<=(number const &v) const { return mpfr_lessequal_p(data->val, v.data->val); }
  bool operator>=(number const &v) const { return mpfr_greaterequal_p(data->val, v.data->val); }
  bool operator<(number const &v) const { return mpfr_less_p(data->val, v.data->val); }
  bool operator>(number const &v) const { return mpfr_greater_p(data->val, v.data->val); }
  bool operator==(number const &v) const { return mpfr_equal_p(data->val, v.data->val); }
  bool operator!=(number const &v) const { return mpfr_lessgreater_p(data->val, v.data->val); }
  number operator-() const;
  static number pos_inf, neg_inf;
};

number const &min(number const &x, number const &y);
number const &max(number const &x, number const &y);

namespace boost { namespace numeric { namespace interval_lib { namespace user {

inline bool is_zero(::number const &v) { return mpfr_sgn(v.data->val) == 0; }
inline bool is_neg(::number const &v)  { return mpfr_sgn(v.data->val) < 0; }
inline bool is_pos(::number const &v)  { return mpfr_sgn(v.data->val) > 0; }

} } } }

struct split_point
{
  number pt;
  bool inleft;
  split_point(number const &n, bool b): pt(n), inleft(b) {}
  bool operator<(split_point const &s) const
  {
    int c = mpfr_cmp(pt.mpfr_data(), s.pt.mpfr_data());
    return c < 0 || (c == 0 && !inleft && s.inleft);
  }
  bool operator==(split_point const &s) const
  { return pt == s.pt && inleft == s.inleft; }
};

#endif // NUMBER_REAL_HPP
