/*
   Copyright (C) 2004 - 2013 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <iostream>
#include <boost/preprocessor/cat.hpp>
#include "backends/backend.hpp"
#include "utils.hpp"
#include "numbers/real.hpp"
#include "numbers/interval.hpp"
#include "numbers/interval_utility.hpp"
#include "parser/ast.hpp"
#include "proofs/rewriting.hpp"
#include "proofs/updater.hpp"

extern backend *proof_generator;
extern bool parameter_constrained;

ast_number const *token_zero, *token_one;

RUN_ONCE(load_numbers) {
  ast_number num;
  num.base = 0;
  num.exponent = 0;
  token_zero = normalize(num);
  num.base = 1;
  num.exponent = 0;
  num.mantissa = "+1";
  token_one = normalize(num);
}

// REWRITING
struct rewriting_scheme: proof_scheme
{
  predicated_real rewritten;
  pattern_cond_vect conditions;
  preal_vect needed_reals(predicated_real const &, pattern_cond_vect const &) const;
  rewriting_scheme(predicated_real const &src, predicated_real const &dst, char const *n, pattern_cond_vect const &c)
    : proof_scheme(src, needed_reals(dst, c), n, UPD_COPY), rewritten(dst), conditions(c) {}
  virtual void compute(property const[], property &, std::string &) const;
};

preal_vect rewriting_scheme::needed_reals(predicated_real const &d,
  pattern_cond_vect const &c) const
{
  preal_vect res;
  for (pattern_cond_vect::const_iterator i = c.begin(), i_end = c.end();
       i != i_end; ++i)
    res.push_back(predicated_real(i->real, i->type == COND_NZ ? PRED_NZR : PRED_BND));
  if (!d.null()) res.push_back(d);
  return res;
}

void rewriting_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  int j = 0;
  bool fail = false;
  for (pattern_cond_vect::const_iterator i = conditions.begin(),
       i_end = conditions.end(); i != i_end; ++i, ++j)
  {
    if (i->type == COND_NZ) continue;
    interval const &bnd = hyps[j].bnd();
    number n(i->value);
    bool good = true;
    switch (i->type)
    {
      case COND_LE: good = n >= upper(bnd); break;
      case COND_LT: good = n >  upper(bnd); break;
      case COND_GE: good = n <= lower(bnd); break;
      case COND_GT: good = n <  lower(bnd); break;
      case COND_NE: good = n > upper(bnd) || n < lower(bnd); break;
      case COND_NZ: break;
    }
    if (good) continue;
    if (parameter_constrained) { res.clear(); return; }
    fail = true;
  }
  if (!rewritten.null())
  {
    // straight rewriting, a property is actually forwarded
    if (res.real.pred_bnd()) {
      res.bnd() = hyps[j].bnd();
    } else if (res.real.pred_cst()) {
      res.cst() = hyps[j].cst();
    }
  }
  if (fail) name = "$FALSE";
}

static rewriting_scheme *generate_rewriting_scheme(predicated_real const &src,
  predicated_real const &dst, std::string const &name, rewriting_rule const *rule,
  ast_real_vect const &holders)
{
  for (pattern_excl_vect::const_iterator i = rule->excl.begin(),
       i_end = rule->excl.end(); i != i_end; ++i)
  {
    if (rewrite(i->first, holders) == rewrite(i->second, holders))
      return NULL;
  }

  pattern_cond_vect c(rule->cond);
  for (pattern_cond_vect::iterator i = c.begin(), end = c.end(); i != end; ++i)
    i->real = rewrite(i->real, holders);
  return new rewriting_scheme(src, dst, name.c_str(), c);
}

struct rewriting_factory: scheme_factory
{
  std::string name;
  rewriting_rule const *rule;
  pattern_cond_vect cond;
  virtual proof_scheme *operator()(predicated_real const &, ast_real_vect const &) const;
  rewriting_factory(ast_real const *src, ast_real const *dst, std::string const &n,
    rewriting_rule const *r, pattern_cond_vect const &c)
  : scheme_factory(predicated_real(src, unhide(dst), PRED_EQL)), name(n), rule(r), cond(c) {}
};

proof_scheme *rewriting_factory::operator()(predicated_real const &src,
  ast_real_vect const &holders) const
{
  if (rule)
    return generate_rewriting_scheme(src, predicated_real(), name, rule, holders);
  // user-defined rule, no exclusions, nor placeholders in conditions
  return new rewriting_scheme(src, predicated_real(), name.c_str(), cond);
}

struct bnd_rewriting_factory: scheme_factory
{
  predicated_real dst;
  std::string name;
  rewriting_rule const *rule;
  virtual proof_scheme *operator()(predicated_real const &, ast_real_vect const &) const;
  bnd_rewriting_factory(predicated_real const &p1, predicated_real const &p2,
    std::string const &n, rewriting_rule const *r)
  : scheme_factory(p1), dst(p2), name(n), rule(r) {}
};

proof_scheme *bnd_rewriting_factory::operator()(predicated_real const &src,
  ast_real_vect const &holders) const
{
  predicated_real d(rewrite(dst.real(), holders), dst.real2() ? rewrite(dst.real2(), holders) : NULL, dst.pred());
  return generate_rewriting_scheme(src, d, name, rule, holders);
}

// PROXY REWRITING
struct proxy_rewriting_scheme: proof_scheme
{
  virtual void compute(property const[], property &, std::string &) const;
  proxy_rewriting_scheme(predicated_real const &r, preal_vect const &p, char const *n)
    : proof_scheme(r, p, n, UPD_COPY) {}
};

void proxy_rewriting_scheme::compute(property const hyps[], property &res, std::string &) const
{
  res = hyps[1];
  res.real = real;
}

struct proxy_rewriting_factory: scheme_factory
{
  predicated_real dst;
  ast_real const *rsrc, *rdst;
  std::string name;
  pattern_excl_vect const *excl;
  virtual proof_scheme *operator()(predicated_real const &, ast_real_vect const &) const;
  proxy_rewriting_factory(ast_real const *r1, ast_real const *r2,
    predicated_real const &p1, predicated_real const &p2, std::string const &n,
    pattern_excl_vect const *e)
  : scheme_factory(p1), dst(p2), rsrc(r1), rdst(r2), name(n), excl(e) {}
};

proof_scheme *proxy_rewriting_factory::operator()(predicated_real const &src,
  ast_real_vect const &holders) const
{
  if (excl)
  {
    for (pattern_excl_vect::const_iterator i = excl->begin(),
         i_end = excl->end(); i != i_end; ++i)
    {
      if (rewrite(i->first, holders) == rewrite(i->second, holders))
        return NULL;
    }
  }

  predicate_type t = dst.pred();
  ast_real const *r = rewrite(dst.real(), holders);
  preal_vect needed;
  needed.push_back(predicated_real(rewrite(rsrc, holders), rewrite(unhide(rdst), holders), PRED_EQL));
  needed.push_back(t == PRED_REL
    ? predicated_real(r, rewrite(dst.real2(), holders), t)
    : predicated_real(r, t));
  return new proxy_rewriting_scheme(src, needed, name.c_str());
}

// REWRITING GENERATION
static void generate_all_proxy_rewrite(ast_real const *src,
  ast_real const *dst, pattern_excl_vect const *e)
{
  typedef predicated_real pr;
  static struct { predicate_type t; char const *n; } const ths[] = {
    { PRED_BND, "bnd_rewrite" },
    { PRED_ABS, "abs_rewrite" },
    { PRED_FIX, "fix_rewrite" },
    { PRED_FLT, "flt_rewrite" },
    { PRED_NZR, "nzr_rewrite" },
  };
  for (unsigned i = 0; i != sizeof(ths) / sizeof(ths[0]); ++i)
    new proxy_rewriting_factory(src, dst, pr(src, ths[i].t), pr(dst, ths[i].t), ths[i].n, e);
  pattern free(count_missing(src));
  new proxy_rewriting_factory(src, dst, pr(src, free, PRED_REL),
    pr(dst, free, PRED_REL), "rel_rewrite_1", e);
  new proxy_rewriting_factory(src, dst, pr(free, src, PRED_REL),
    pr(free, dst, PRED_REL), "rel_rewrite_2", e);
}

RUN_ONCE(approximate_rewrite) {
  generate_all_proxy_rewrite(pattern(1), pattern(0), NULL);
}

void register_user_rewrite(ast_real const *r1, ast_real const *r2, hint_cond_vect *hc)
{
  pattern_cond_vect pc;
  if (hc)
  {
    for (hint_cond_vect::const_iterator i = hc->begin(),
         i_end = hc->end(); i != i_end; ++i)
    {
      hint_cond const *c = *i;
      pattern_cond cond;
      cond.real = c->real;
      cond.value = atoi(c->value->mantissa.c_str());
      cond.type = c->type == COND_NE && cond.value == 0 ? COND_NZ : c->type;
      pc.push_back(cond);
      delete c;
    }
  }
  std::string name = proof_generator ? proof_generator->rewrite(r1, r2, pc) : "$AXIOM";
  new rewriting_factory(r1, r2, name, NULL, pc);
  generate_all_proxy_rewrite(r1, r2, NULL);
}

rewriting_vect rewriting_rules;

rewriting_rule::rewriting_rule
  (predicated_real const &p1, predicated_real const &p2, std::string const &n,
   pattern_cond_vect const &c, pattern_excl_vect const &e)
  : src(p1), dst(p2), cond(c), excl(e)
{
  rewriting_rules.push_back(this);
  new bnd_rewriting_factory(p1, p2, n, this);
}

// PATTERN OPERATIONS
pattern_cond_vect operator&&(pattern_cond_vect const &v, pattern_cond const &c) {
  pattern_cond_vect res(v);
  res.push_back(c);
  return res;
}

pattern_excl operator^(pattern const &a, pattern const &b) {
  return pattern_excl(a, b);
}

pattern_excl_vect operator&&(pattern_excl_vect const &v, pattern_excl const &c) {
  pattern_excl_vect res(v);
  res.push_back(c);
  return res;
}

static pattern a(0), b(1), c(2), d(3), a_b(-1), one(token_one);

#define abs pattern::abs
#define sqrt pattern::sqrt
#define log pattern::log
#define exp pattern::exp
#define log2 pattern::log2
#define exp2 pattern::exp2
#define hide pattern::hide

#define REWRITING_NAME BOOST_PP_CAT(rewriting_rule_,__LINE__)

/*
Naming convention: operator name followed by
  x (expand term)      f (factor term)      m (mix)
  a (approximate expr) e (accurate expr)    i (irrelevant)
  l (left hand side)   r (right hand side)  b (both)
  s (absolute error)   q (relative error)   e (equality)
*/

#define REWRITE(name,p1,p2) \
  static rewriting_rule REWRITING_NAME \
    (predicated_real(p1, PRED_BND), predicated_real(p2, PRED_BND),\
     #name, pattern_cond_vect(), pattern_excl_vect())
#define REWRIT3(name,p1,p2,cond) \
  static rewriting_rule REWRITING_NAME \
    (predicated_real(p1, PRED_BND), predicated_real(p2, PRED_BND),\
     #name, pattern_cond_vect() && cond, pattern_excl_vect())
#define REWRITe(name,p1,p2,excl) \
  static rewriting_rule REWRITING_NAME \
    (predicated_real(p1, PRED_BND), predicated_real(p2, PRED_BND),\
     #name, pattern_cond_vect(), pattern_excl_vect() && excl)
#define REWRIT9(name,p1,p2,cond,excl) \
  static rewriting_rule REWRITING_NAME \
    (predicated_real(p1, PRED_BND), predicated_real(p2, PRED_BND),\
     #name, pattern_cond_vect() && cond, pattern_excl_vect() && excl)

// OPP

REWRITe(opp_mibs,
	-a - -b,
	hide(-(a - b)),
	a ^ b);

// ADD

REWRITE(add_xals,
	b + c,
	hide((b - a) + (a + c)));

REWRITE(add_xars,
	c + b,
	hide((c + a) + (b - a)));

REWRITe(add_mibs,
	(a + b) - (c + d),
	hide((a - c) + (b - d)),
	a ^ c && b ^ d);

REWRITe(add_fils,
	(a + b) - (a + c),
	b - c,
	b ^ c);

REWRITe(add_firs,
	(a + b) - (c + b),
	a - c,
	a ^ c);

REWRIT9(add_filq,
	((a + b) - (a + c)) / (a + c),
	(b - c) / (a + c),
	~(a + c),
	b ^ c);

REWRIT9(add_firq,
	((a + b) - (c + b)) / (c + b),
	(a - c) / (c + b),
	~(c + b),
	a ^ c);

REWRITe(add_filrs,
	a - (b + a),
	-b,
	a ^ b);

REWRITe(add_firls,
	(a + b) - a,
	b,
	a ^ b);

// SUB

REWRITe(sub_xals,
	b - c,
	hide((b - a) + (a - c)),
	a ^ c && b ^ c);

REWRITe(sub_xars,
	c - b,
	hide((c - a) - (b - a)),
	b ^ c); // no a^c so that the rule can be used to revert a-b

REWRITe(sub_mibs,
	(a - b) - (c - d),
	hide((a - c) - (b - d)),
	a ^ c && b ^ d);

REWRITe(sub_fils,
	(a - b) - (a - c),
	hide(-(b - c)),
	b ^ c);

REWRITe(sub_firs,
	(a - b) - (c - b),
	a - c,
	a ^ c);

REWRIT9(sub_filq,
	((a - b) - (a - c)) / (a - c),
	hide(-((b - c) / (a - c))),
	~(a - c),
	b ^ c);

REWRIT9(sub_firq,
	((a - b) - (c - b)) / (c - b),
	(a - c) / (c - b),
	~(c - b),
	a ^ c);

// MUL

REWRITE(mul_xals,
	b * c,
	hide(hide((b - a) * c) + a * c));

REWRITE(mul_xars,
	c * b,
	hide(hide(c * (b - a)) + c * a));

REWRITe(mul_fils,
	a * b - a * c,
	hide(a * (b - c)),
	b ^ c);

REWRITe(mul_firs,
	a * b - c * b,
	hide((a - c) * b),
	a ^ c);

REWRITe(mul_mars,
	a * b - c * d,
	hide(hide(a * (b - d)) + hide((a - c) * d)),
	a ^ c && b ^ d);

REWRITe(mul_mals,
	a * b - c * d,
	hide(hide((a - c) * b) + hide(c * (b - d))),
	a ^ c && b ^ d);

REWRITe(mul_mabs,
	a * b - c * d,
	hide(hide(hide(a * (b - d)) + hide((a - c) * b)) - hide((a - c) * (b - d))),
	a ^ c && b ^ d);

REWRITe(mul_mibs,
	a * b - c * d,
	hide(hide(hide(c * (b - d)) + hide((a - c) * d)) + hide((a - c) * (b - d))),
	a ^ c && b ^ d);

REWRITe(mul_filq,
	(a * b - a * c) / (a * c),
	(b - c) / c,
	b ^ c);

REWRITe(mul_firq,
	(a * b - c * b) / (c * b),
	(a - c) / c,
	a ^ c);

// DIV

REWRITe(div_firq,
	(a / b - c / b) / (c / b),
	(a - c) / c,
	a ^ c);

REWRIT9(div_xals,
	b / c,
	hide((b - a) / c + a / c),
	~c,
	a ^ c && b ^ c);

REWRIT3(div_fir,
	(a * b) / b,
	a,
	~b);

REWRIT3(div_fil,
	(a * b) / a,
	b,
	~a);

REWRITe(div_mabs,
	(a / b - c / d),
	(((a - c) / b) - ((b - d) * (c / (b * d)))),
	a ^ c);

REWRITe(div_firs,
	((c / a) - (c / b)),
	c * (-(a - b))/(a * b),
	a ^ b);

// SQRT

REWRIT9(sqrt_mibs,
	sqrt(a) - sqrt(b),
	hide((a - b) / hide(sqrt(a) + sqrt(b))),
	a >= 0 && b >= 0,
	a ^ b);

REWRIT9(sqrt_mibq,
	(sqrt(a) - sqrt(b)) / sqrt(b),
	hide(sqrt(hide(one + (a - b) / b)) - one),
	a >= 0 && b > 0,
	a ^ b);

// EXP

REWRITe(exp_mibq,
	(exp(a) - exp(b)) / exp(b),
	hide(exp(a - b) - one),
	a ^ b);

REWRITe(exp_mibs,
	(exp(a) - exp(b)),
	(exp(b)*(exp(a-b) - one)),
	a ^ b);

REWRITE(exp_mul,
	(exp(a)*exp(b)),
	(exp(a+b)));

REWRITE(exp_div,
	(exp(a)/exp(b)),
	(exp(a-b)));

REWRITE(exp_xals_m,
	(exp(a+b)),
	(exp(a)*exp(b)));

REWRITE(exp_xals_d,
	(exp(a-b)),
	(exp(a)/exp(b)));

// EXP2

REWRITe(exp2_mibq,
	(exp2(a) - exp2(b)) / exp2(b),
	hide(exp2(a - b) - one),
	a ^ b);

REWRITe(exp2_mibs,
	(exp2(a) - exp2(b)),
	(exp2(b)*(exp2(a-b) - one)),
	a ^ b);

REWRITE(exp2_mul,
	(exp2(a)*exp2(b)),
	(exp2(a+b)));

REWRITE(exp2_div,
	(exp2(a)/exp2(b)),
	(exp2(a-b)));

REWRITE(exp2_xals_m,
	(exp2(a+b)),
	(exp2(a)*exp2(b)));

REWRITE(exp2_xals_d,
	(exp2(a-b)),
	(exp2(a)/exp2(b)));


// LOG

REWRIT9(log_mibs,
	(log(a) - log(b)),
	hide(log(hide(one + ((a - b) / b)))),
	a > 0 && b > 0,
	a ^ b);

REWRIT3(log_xals_m,
	a - log(b),
	log(one+(exp(a)-b)/b),
	b > 0);

REWRIT3(log_xals_p,
	a + log(b),
	log(exp(a)*b),
	b > 0);
	
REWRIT3(log_xars,
	log(b)-a,
	log(one+(b-exp(a))/exp(a)),
	b > 0);	

// LOG2

REWRIT9(log2_mibs,
	(log2(a) - log2(b)),
	hide(log2(hide(one + ((a - b) / b)))),
	a > 0 && b > 0,
	a ^ b);

REWRIT3(log2_xals_m,
	a - log2(b),
	log2(one+(exp2(a)-b)/b),
	b > 0);

REWRIT3(log2_xals_p,
	a + log2(b),
	log2(exp2(a)*b),
	b > 0);
	
REWRIT3(log2_xars,
	log2(b)-a,
	log2(one+(b-exp2(a))/exp2(a)),
	b > 0);	

// ERR

REWRITe(sub_xals, //actually err_xers
	c - a,
	hide((c - b) + (b - a)),
	a ^ c && b ^ c);

/* bad bad Zoot
REWRIT9(err_xabq,
	a / b,
	one + (a - b) / b,
	~b,
	a ^ b);
*/

/* ???
REWRIT9(err_fabq,
	one + (a - b) / b,
	a / b,
	~b,
	a ^ b);
*/

// VAL

REWRITE(val_xabs,
	b,
	hide(a + (b - a)));

REWRITE(val_xebs,
	a_b,
	hide(b - (b - a)));

REWRIT3(val_xabq,
	b,
	hide(a * hide(one + (b - a) / a)),
	~a);

REWRIT3(val_xebq,
	a_b,
	hide(b / hide(one + (b - a) / a)),
	~a && ~b);

// BLI

REWRIT3(square_sqrt,
	sqrt(a) * sqrt(a),
	a,
	a >= 0);

REWRIT3(addf_1,
	a / (a + b),
	hide(one / hide(one + b / a)),
	~a && ~(a + b));

REWRIT9(addf_2,
	a / (a + b),
	hide(one - b / (a + b)),
	~(a + b),
	a ^ b);

REWRIT9(addf_3,
	a / (a - b),
	hide(one / hide(one - b / a)),
	~a && ~(a - b),
	a ^ b);

REWRIT9(addf_4,
	a / (a - b),
	hide(one + b / (a - b)),
	~(a - b),
	a ^ b);

REWRIT9(addf_5,
	b / (a + b),
	hide(one / hide(a / b + one)),
	~b && ~(a + b),
	a ^ b);

REWRIT9(addf_6,
	b / (a + b),
	hide(one - a / (a + b)),
	~(a + b),
	a ^ b);

REWRIT9(addf_7,
	b / (a - b),
	hide(one / hide(a / b - one)),
	~b && ~(a - b),
	a ^ b);

REWRIT9(addf_8,
	b / (a - b),
	hide(a / (a - b) - one),
	~(a - b),
	a ^ b);

#undef REWRITE
#undef REWRIT3
#undef REWRITe
#undef REWRIT9

#define REWRITE(name,lhs1,rhs1,lhs2,rhs2) \
  static rewriting_rule REWRITING_NAME \
    (predicated_real(lhs1, rhs1, PRED_REL), predicated_real(lhs2, rhs2, PRED_REL),\
     #name, pattern_cond_vect(), pattern_excl_vect())
#define REWRIT3(name,lhs1,rhs1,lhs2,rhs2,cond) \
  static rewriting_rule REWRITING_NAME \
    (predicated_real(lhs1, rhs1, PRED_REL), predicated_real(lhs2, rhs2, PRED_REL),\
     #name, pattern_cond_vect() && cond, pattern_excl_vect())
#define REWRITe(name,lhs1,rhs1,lhs2,rhs2,excl) \
  static rewriting_rule REWRITING_NAME \
    (predicated_real(lhs1, rhs1, PRED_REL), predicated_real(lhs2, rhs2, PRED_REL),\
     #name, pattern_cond_vect(), pattern_excl_vect() && excl)
#define REWRIT9(name,lhs1,rhs1,lhs2,rhs2,cond,excl) \
  static rewriting_rule REWRITING_NAME \
    (predicated_real(lhs1, rhs1, PRED_REL), predicated_real(lhs2, rhs2, PRED_REL),\
     #name, pattern_cond_vect() && cond, pattern_excl_vect() && excl)

REWRITe(opp_fibq,
	-a, -b,
	a, b,
	a ^ b);

REWRITe(mul_filq,
	a * b, a * c,
	b, c,
	b ^ c);

REWRITe(mul_firq,
	a * b, c * b,
	a, c,
	a ^ c);

REWRITe(div_firq,
	a / b, c / b,
	a, c,
	a ^ c);

#undef REWRITE
#undef REWRIT3
#undef REWRITe
#undef REWRIT9

#define REWRITE(name,lhs1,rhs1,lhs2,rhs2) \
  static rewriting_rule REWRITING_NAME \
    (predicated_real(lhs1, rhs1, PRED_EQL), predicated_real(lhs2, rhs2, PRED_EQL),\
     #name, pattern_cond_vect(), pattern_excl_vect())
#define REWRIT3(name,lhs1,rhs1,lhs2,rhs2,cond) \
  static rewriting_rule REWRITING_NAME \
    (predicated_real(lhs1, rhs1, PRED_EQL), predicated_real(lhs2, rhs2, PRED_EQL),\
     #name, pattern_cond_vect() && cond, pattern_excl_vect())
#define REWRITe(name,lhs1,rhs1,lhs2,rhs2,excl) \
  static rewriting_rule REWRITING_NAME \
    (predicated_real(lhs1, rhs1, PRED_EQL), predicated_real(lhs2, rhs2, PRED_EQL),\
     #name, pattern_cond_vect(), pattern_excl_vect() && excl)
#define REWRIT9(name,lhs1,rhs1,lhs2,rhs2,cond,excl) \
  static rewriting_rule REWRITING_NAME \
    (predicated_real(lhs1, rhs1, PRED_EQL), predicated_real(lhs2, rhs2, PRED_EQL),\
     #name, pattern_cond_vect() && cond, pattern_excl_vect() && excl)

REWRITe(opp_fibe,
	-a, -b,
	a, b,
	a ^ b);

REWRITe(add_file,
	a + b, a + c,
	b, c,
	b ^ c);

REWRITe(add_fire,
	a + b, c + b,
	a, c,
	a ^ c);

REWRITe(sub_file,
	a - b, a - c,
	b, c,
	b ^ c);

REWRITe(sub_fire,
	a - b, c - b,
	a, c,
	a ^ c);

REWRITe(mul_file,
	a * b, a * c,
	b, c,
	b ^ c);

REWRITe(mul_fire,
	a * b, c * b,
	a, c,
	a ^ c);

REWRITe(div_file,
	a / b, a / c,
	b, c,
	b ^ c);

REWRITe(div_fire,
	a / b, c / b,
	a, c,
	a ^ c);
