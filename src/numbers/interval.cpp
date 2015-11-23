/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <cassert>
#include <boost/numeric/interval/arith.hpp>
#include <boost/numeric/interval/arith2.hpp>
#include <boost/numeric/interval/arith3.hpp>
#include <boost/numeric/interval/transc.hpp>
#include <boost/numeric/interval/checking.hpp>
#include <boost/numeric/interval/interval.hpp>
#include <boost/numeric/interval/policies.hpp>
#include <boost/numeric/interval/rounded_arith.hpp>
#include <boost/numeric/interval/utility.hpp>
#include "numbers/interval.hpp"
#include "numbers/interval_arith.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"

class real_policies {
  typedef number T;
public:
# define RES(name) number_base *name = new number_base()
  struct rounding {
    static T conv_down(int v)		{ RES(w); mpfr_set_si(w->val, v, GMP_RNDD); return T(w); }
    static T conv_up  (int v)		{ RES(w); mpfr_set_si(w->val, v, GMP_RNDU); return T(w); }
    static T conv_down(T const &v)	{ return v; }
    static T conv_up  (T const &v)	{ return v; }
    static T opp_down(T const &v)	{ RES(w); mpfr_neg(w->val, v.data->val, GMP_RNDD); return T(w); }
    static T opp_up  (T const &v)	{ RES(w); mpfr_neg(w->val, v.data->val, GMP_RNDU); return T(w); }
    static T sqrt_down(T const &v)	{ RES(w); mpfr_sqrt(w->val, v.data->val, GMP_RNDD); return T(w); }
    static T sqrt_up  (T const &v)	{ RES(w); mpfr_sqrt(w->val, v.data->val, GMP_RNDU); return T(w); }
    static T log_down (T const &v)      { RES(w); mpfr_log(w->val, v.data->val, GMP_RNDD); return T(w); }
    static T log_up   (T const &v)      { RES(w); mpfr_log(w->val, v.data->val, GMP_RNDU); return T(w); }
    static T exp_down (T const &v)      { RES(w); mpfr_exp(w->val, v.data->val, GMP_RNDD); return T(w); }
    static T exp_up   (T const &v)      { RES(w); mpfr_exp(w->val, v.data->val, GMP_RNDU); return T(w); }
    static T log2_down (T const &v)      { RES(w); mpfr_log2(w->val, v.data->val, GMP_RNDD); return T(w); }
    static T log2_up   (T const &v)      { RES(w); mpfr_log2(w->val, v.data->val, GMP_RNDU); return T(w); }
    static T exp2_down (T const &v)      { RES(w); mpfr_exp2(w->val, v.data->val, GMP_RNDD); return T(w); }
    static T exp2_up   (T const &v)      { RES(w); mpfr_exp2(w->val, v.data->val, GMP_RNDU); return T(w); }
#   define BINARY_FUNC(name) \
    static T name##_down(T const &x, T const &y) \
    { RES(z); mpfr_##name(z->val, x.data->val, y.data->val, GMP_RNDD); return T(z); } \
    static T name##_up  (T const &x, T const &y) \
    { RES(z); mpfr_##name(z->val, x.data->val, y.data->val, GMP_RNDU); return T(z); }
    BINARY_FUNC(add);
    BINARY_FUNC(sub);
    BINARY_FUNC(mul);
    BINARY_FUNC(div);
#   undef BINARY_FUNC
    static T median(T const &x, T const &y) {
      RES(w); mpfr_add(w->val, x.data->val, y.data->val, GMP_RNDN);
      mpfr_div_2ui(w->val, w->val, 1, GMP_RNDN); return T(w);
    }
    typedef rounding unprotected_rounding;
  };
  struct checking {
    static bool is_nan(int) { return false; }
    static bool is_nan(double v) { return (v != v); }
    static bool is_nan(T const &v) { return mpfr_nan_p(v.data->val); }
    static T empty_lower() { return T(); }
    static T empty_upper() { return T(); }
    static T pos_inf() { return T::pos_inf; }
    static T neg_inf() { return T::neg_inf; }
    static T nan() { RES(w); return T(w); }
    static bool is_empty(T const &x, T const &y) { return !(x <= y); }
  };
# undef RES
};

typedef boost::numeric::interval< number, real_policies > _interval_base;

class interval_base {
  interval_base(interval_base const &i);
 public:
  _interval_base value;
  mutable ref_counter_t ref_counter;
  interval_base() {}
  interval_base(_interval_base const &v): value(v) {}
  interval_base const *clone() const { ref_counter.incr(); return this; }
  void destroy() const { if (ref_counter.decr()) delete this; }
  friend class interval;
};

interval_base *interval::unique() const {
  if (base->ref_counter.nb != 1) {
    interval_base *b = new interval_base(base->value);
    base->destroy();
    base = b;
  }
  return const_cast< interval_base * >(base);
}

interval::interval(interval const &i): base(i.base ? i.base->clone() : 0) {}
interval::~interval() { if (base) base->destroy(); }

interval &interval::operator=(interval const &i) {
  if (this != &i) {
    if (base) base->destroy();
    base = i.base ? i.base->clone() : 0;
  }
  return *this;
}

interval::interval(number const &l, number const &u) {
  base = new interval_base(_interval_base(l, u));
}

#define plip(i) i.base->value
#define plop(i) interval(new interval_base(i))
#define pltp base->value
#define plup u.base->value
#define plvp v.base->value

interval zero() {
  return plop(_interval_base());
}

bool is_empty(interval const &u) {
  assert(u.base);
  return empty(plup);
}

bool is_singleton(interval const &u) {
  assert(u.base);
  return singleton(plup);
}

bool contains_zero(interval const &u) {
  if (!u.base) return true;
  return in_zero(plup);
}

bool is_zero(interval const &u) {
  assert(u.base);
  return singleton(plup) && in_zero(plup);
}

bool is_bounded(interval const &u) {
  assert(u.base);
  return plup.lower() != number::neg_inf && plup.upper() != number::pos_inf;
}

interval hull(interval const &u, interval const &v) {
  assert(u.base && v.base);
  return plop(hull(plup, plvp));
}

interval intersect(interval const &u, interval const &v) {
  assert(u.base && v.base);
  return plop(intersect(plup, plvp));
}

std::pair< interval, interval > split(interval const &u) {
  assert(u.base);
  number m = median(plup);
  return std::make_pair(plop(_interval_base(plup.lower(), m)),
                        plop(_interval_base(m, plup.upper())));
}

std::pair< interval, interval > split(interval const &u, double f) {
  assert(u.base);
  number_base *d = new number_base;
  mpfr_t tmp;
  mpfr_init2(tmp, parameter_internal_precision);
  mpfr_set_d(tmp, 1 - f, GMP_RNDN);
  mpfr_mul(d->val, tmp, plup.lower().data->val, GMP_RNDN);
  mpfr_set_d(tmp, f, GMP_RNDN);
  mpfr_mul(tmp, tmp, plup.upper().data->val, GMP_RNDN);
  mpfr_add(d->val, d->val, tmp, GMP_RNDN);
  mpfr_clear(tmp);
  number m(d);
  return std::make_pair(plop(_interval_base(plup.lower(), m)),
                        plop(_interval_base(m, plup.upper())));
}

bool interval::operator<=(interval const &v) const {
  if (!v.base) return true;
  if (!base) return false;
  return subset(pltp, plvp);
}

bool interval::operator<(interval const &v) const {
  if (!v.base) return true;
  if (!base) return false;
  return proper_subset(pltp, plvp);
}

interval operator-(interval const &u) {
  assert(u.base);
  return plop(-plup);
}

interval operator+(interval const &u, interval const &v) {
  assert(u.base && v.base);
  return plop(plup + plvp);
}

interval operator-(interval const &u, interval const &v) {
  assert(u.base && v.base);
  return plop(plup - plvp);
}

interval operator*(interval const &u, interval const &v) {
  assert(u.base && v.base);
  return plop(plup * plvp);
}

interval operator/(interval const &u, interval const &v) {
  assert(u.base && v.base && !contains_zero(v));
  return plop(plup / plvp);
}

interval abs(interval const &u) {
  assert(u.base);
  return plop(abs(plup));
}

interval square(interval const &u) {
  assert(u.base);
  return plop(square(plup));
}

interval sqrt(interval const &u) {
  assert(u.base);
  return plop(sqrt(plup));
}

interval log(interval const &u) {
  assert(u.base);
  return plop(log(plup));
}

interval exp(interval const &u) {
  assert(u.base);
  return plop(exp(plup));
}

// Need to supply our own implementations for exp2 and log2

namespace boost {
  namespace numeric {
    
    template<class T, class Policies> inline
    interval<T, Policies> exp2(const interval<T, Policies>& x)
    {
      typedef interval<T, Policies> I;
      if (interval_lib::detail::test_input(x))
	return I::empty();
      typename Policies::rounding rnd;
      return I(rnd.exp2_down(x.lower()), rnd.exp2_up(x.upper()), true);
    }
    
    template<class T, class Policies> inline
    interval<T, Policies> log2(const interval<T, Policies>& x)
    {
      typedef interval<T, Policies> I;
      if (interval_lib::detail::test_input(x) ||
	  !interval_lib::user::is_pos(x.upper()))
	return I::empty();
      typename Policies::rounding rnd;
      typedef typename Policies::checking checking;
      T l = !interval_lib::user::is_pos(x.lower())
	? checking::neg_inf() : rnd.log2_down(x.lower());
      return I(l, rnd.log2_up(x.upper()), true);
    }
    
  } // end of namespace numeric
} // end of namespace boost


interval log2(interval const &u) {
  assert(u.base);
  return plop(log2(plup));
}

interval exp2(interval const &u) {
  assert(u.base);
  return plop(exp2(plup));
}

interval from_exponent(int exp, int rnd) {
  number_base *l = new number_base, *u = new number_base;
  if (rnd == 0) {
    mpfr_set_ui_2exp(u->val, 1, exp, GMP_RNDN);
    mpfr_neg(l->val, u->val, GMP_RNDN);
  } else if (rnd < 0) {
    mpfr_set_si_2exp(l->val, -1, exp, GMP_RNDN);
    mpfr_set_ui(u->val, 0, GMP_RNDN);
  } else {
    mpfr_set_ui(l->val, 0, GMP_RNDN);
    mpfr_set_ui_2exp(u->val, 1, exp, GMP_RNDN);
  }
  return interval(number(l), number(u));
}

number const &lower(interval const &u) {
  assert(u.base);
  return plup.lower();
}

number const &upper(interval const &u) {
  assert(u.base);
  return plup.upper();
}

int sign(interval const &u) {
  assert(u.base);
  using namespace boost::numeric::interval_lib::user;
  return !is_neg(plup.lower()) ? 1 : !is_pos(plup.upper()) ? -1 : 0;
}

int sign_strict(interval const &u) {
  assert(u.base);
  using namespace boost::numeric::interval_lib::user;
  return is_pos(plup.lower()) ? 1 : is_neg(plup.upper()) ? -1 : 0;
}

// compute u + v + u * v
interval compose_relative(interval const &u, interval const &v) {
  assert(u.base && v.base);
  typedef real_policies::rounding rnd;
  number const &ul = plup.lower(), &uu = plup.upper(),
               &vl = plvp.lower(), &vu = plvp.upper();
  if (ul < -1 || vl < -1) return interval();
  return interval(rnd::add_down(rnd::add_down(ul, vl), rnd::mul_down(ul, vl)),
                  rnd::add_up  (rnd::add_up  (uu, vu), rnd::mul_up  (uu, vu)));
}

// compute (u - v) / (1 + v)
interval compose_relative_inv(interval const &u, interval const &v) {
  assert(u.base && v.base);
  typedef real_policies::rounding rnd;
  number const &ul = plup.lower(), &uu = plup.upper(),
               &vl = plvp.lower(), &vu = plvp.upper();
  if (ul < -1 || vl <= -1) return interval();
  return interval(rnd::div_down(rnd::sub_down(ul, vu), rnd::add_up  (number(1), vu)),
                  rnd::div_up  (rnd::sub_up  (uu, vl), rnd::add_down(number(1), vl)));
}

// compute u * w + v * (1 - w)
interval add_relative(interval const &u, interval const &v, interval const &w) {
  assert(u.base && v.base && w.base);
  number const &wl = plip(w).lower(), &wu = plip(w).upper();
  #define one_minus(x) boost::numeric::interval_lib::sub< _interval_base >(number(1), x)
  return plop(hull(wl * plup + one_minus(wl) * plvp, wu * plup + one_minus(wu) * plvp));
  #undef one_minus
}
