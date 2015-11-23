/*
   Copyright (C) 2004 - 2013 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include "numbers/interval_arith.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "parser/pattern.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/schemes.hpp"
#include "proofs/updater.hpp"

static preal_vect one_needed(ast_real const *r) {
  return preal_vect(1, predicated_real(r, PRED_BND));
}

static bool is_changing_sign(ast_real const *r)
{
  real_op const *p = boost::get< real_op const >(r);
  return p && (p->type == UOP_ABS || p->type == UOP_NEG);
}

bool is_hidden(ast_real const *r)
{
  return boost::get< hidden_real const >(r);
}

// ABSOLUTE_ERROR
REGISTER_SCHEME_BEGIN(absolute_error);
  function_class const *function;
  absolute_error_scheme(ast_real const *r, function_class const *f)
    : proof_scheme(predicated_real(r, PRED_BND), preal_vect(), ""), function(f) {}
REGISTER_SCHEME_END(absolute_error);

void absolute_error_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  res.bnd() = function->absolute_error(name);
}

proof_scheme *absolute_error_scheme::factory(ast_real const *real)
{
  ast_real const *holders[2];
  function_class const *f = absolute_rounding_error(real, holders);
  if (!f || !(f->theorem_mask & function_class::TH_ABS)) return NULL;
  return new absolute_error_scheme(real, f);
}

// ABSOLUTE_ERROR_FROM_EXACT_BND
REGISTER_SCHEME_BEGIN(absolute_error_from_exact_bnd);
  function_class const *function;
  absolute_error_from_exact_bnd_scheme(ast_real const *r, ast_real const *e, function_class const *f)
    : proof_scheme(predicated_real(r, PRED_BND), one_needed(e), ""), function(f) {}
REGISTER_SCHEME_END(absolute_error_from_exact_bnd);

void absolute_error_from_exact_bnd_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  res.bnd() = function->absolute_error_from_exact_bnd(hyps[0].bnd(), name);
}

proof_scheme *absolute_error_from_exact_bnd_scheme::factory(ast_real const *real)
{
  ast_real const *holders[2];
  function_class const *f = absolute_rounding_error(real, holders);
  if (!f || !(f->theorem_mask & function_class::TH_ABS_EXA_BND)) return NULL;
  return new absolute_error_from_exact_bnd_scheme(real, holders[0], f);
}

// ABSOLUTE_ERROR_FROM_EXACT_ABS
REGISTER_SCHEME_BEGIN(absolute_error_from_exact_abs);
  function_class const *function;
  absolute_error_from_exact_abs_scheme(ast_real const *r, predicated_real const &e, function_class const *f)
    : proof_scheme(predicated_real(r, PRED_BND), preal_vect(1, e), ""), function(f) {}
REGISTER_SCHEME_END(absolute_error_from_exact_abs);

void absolute_error_from_exact_abs_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  res.bnd() = function->absolute_error_from_exact_abs(hyps[0].bnd(), name);
}

proof_scheme *absolute_error_from_exact_abs_scheme::factory(ast_real const *real)
{
  ast_real const *holders[2];
  function_class const *f = absolute_rounding_error(real, holders);
  if (!f || !(f->theorem_mask & function_class::TH_ABS_EXA_ABS)) return NULL;
  return new absolute_error_from_exact_abs_scheme(real, predicated_real(holders[0], PRED_ABS), f);
}

// ABSOLUTE_ERROR_FROM_APPROX_BND
REGISTER_SCHEME_BEGIN(absolute_error_from_approx_bnd);
  function_class const *function;
  absolute_error_from_approx_bnd_scheme(ast_real const *r, ast_real const *a, function_class const *f)
    : proof_scheme(predicated_real(r, PRED_BND), one_needed(a), ""), function(f) {}
REGISTER_SCHEME_END(absolute_error_from_approx_bnd);

void absolute_error_from_approx_bnd_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  res.bnd() = function->absolute_error_from_approx_bnd(hyps[0].bnd(), name);
}

proof_scheme *absolute_error_from_approx_bnd_scheme::factory(ast_real const *real)
{
  ast_real const *holders[2];
  function_class const *f = absolute_rounding_error(real, holders);
  if (!f || !(f->theorem_mask & function_class::TH_ABS_APX_BND)) return NULL;
  return new absolute_error_from_approx_bnd_scheme(real, holders[1], f);
}

// ABSOLUTE_ERROR_FROM_APPROX_ABS
REGISTER_SCHEME_BEGIN(absolute_error_from_approx_abs);
  function_class const *function;
  absolute_error_from_approx_abs_scheme(ast_real const *r, predicated_real const &a, function_class const *f)
    : proof_scheme(predicated_real(r, PRED_BND), preal_vect(1, a), ""), function(f) {}
REGISTER_SCHEME_END(absolute_error_from_approx_abs);

void absolute_error_from_approx_abs_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  res.bnd() = function->absolute_error_from_approx_abs(hyps[0].bnd(), name);
}

proof_scheme *absolute_error_from_approx_abs_scheme::factory(ast_real const *real)
{
  ast_real const *holders[2];
  function_class const *f = absolute_rounding_error(real, holders);
  if (!f || !(f->theorem_mask & function_class::TH_ABS_APX_ABS)) return NULL;
  return new absolute_error_from_approx_abs_scheme(real, predicated_real(holders[1], PRED_ABS), f);
}

// RELATIVE_ERROR
REGISTER_SCHEME_BEGIN(relative_error);
  function_class const *function;
  relative_error_scheme(predicated_real const &r, function_class const *f)
    : proof_scheme(r, preal_vect(), ""), function(f) {}
REGISTER_SCHEME_END_PREDICATE(relative_error);

void relative_error_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  res.bnd() = function->relative_error(name);
}

proof_scheme *relative_error_scheme::factory(predicated_real const &real)
{
  function_class const *f = relative_rounding_error(real);
  if (!f || !(f->theorem_mask & function_class::TH_REL)) return NULL;
  return new relative_error_scheme(real, f);
}

// RELATIVE_ERROR_FROM_EXACT_BND
REGISTER_SCHEME_BEGIN(relative_error_from_exact_bnd);
  function_class const *function;
  relative_error_from_exact_bnd_scheme(predicated_real const &r, function_class const *f)
    : proof_scheme(r, one_needed(r.real2()), ""), function(f) {}
REGISTER_SCHEME_END_PREDICATE(relative_error_from_exact_bnd);

void relative_error_from_exact_bnd_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  res.bnd() = function->relative_error_from_exact_abs(hyps[0].bnd(), name);
}

proof_scheme *relative_error_from_exact_bnd_scheme::factory(predicated_real const &real)
{
  function_class const *f = relative_rounding_error(real);
  if (!f || !(f->theorem_mask & function_class::TH_REL_EXA_BND)) return NULL;
  return new relative_error_from_exact_bnd_scheme(real, f);
}

// RELATIVE_ERROR_FROM_EXACT_ABS
REGISTER_SCHEME_BEGIN(relative_error_from_exact_abs);
  function_class const *function;
  relative_error_from_exact_abs_scheme(predicated_real const &r, predicated_real const &e, function_class const *f)
    : proof_scheme(r, preal_vect(1, e), ""), function(f) {}
REGISTER_SCHEME_END_PREDICATE(relative_error_from_exact_abs);

void relative_error_from_exact_abs_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  res.bnd() = function->relative_error_from_exact_abs(hyps[0].bnd(), name);
}

proof_scheme *relative_error_from_exact_abs_scheme::factory(predicated_real const &real)
{
  function_class const *f = relative_rounding_error(real);
  if (!f || !(f->theorem_mask & function_class::TH_REL_EXA_ABS)) return NULL;
  return new relative_error_from_exact_abs_scheme(real, predicated_real(real.real2(), PRED_ABS), f);
}

// RELATIVE_ERROR_FROM_APPROX_BND
REGISTER_SCHEME_BEGIN(relative_error_from_approx_bnd);
  function_class const *function;
  relative_error_from_approx_bnd_scheme(predicated_real const &r, function_class const *f)
    : proof_scheme(r, one_needed(r.real()), ""), function(f) {}
REGISTER_SCHEME_END_PREDICATE(relative_error_from_approx_bnd);

void relative_error_from_approx_bnd_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  res.bnd() = function->relative_error_from_approx_bnd(hyps[0].bnd(), name);
}

proof_scheme *relative_error_from_approx_bnd_scheme::factory(predicated_real const &real)
{
  function_class const *f = relative_rounding_error(real);
  if (!f || !(f->theorem_mask & function_class::TH_REL_APX_BND)) return NULL;
  return new relative_error_from_approx_bnd_scheme(real, f);
}

// RELATIVE_ERROR_FROM_APPROX_ABS
REGISTER_SCHEME_BEGIN(relative_error_from_approx_abs);
  function_class const *function;
  relative_error_from_approx_abs_scheme(predicated_real const &r, predicated_real const &a, function_class const *f)
    : proof_scheme(r, preal_vect(1, a), ""), function(f) {}
REGISTER_SCHEME_END_PREDICATE(relative_error_from_approx_abs);

void relative_error_from_approx_abs_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  res.bnd() = function->relative_error_from_approx_abs(hyps[0].bnd(), name);
}

proof_scheme *relative_error_from_approx_abs_scheme::factory(predicated_real const &real)
{
  function_class const *f = relative_rounding_error(real);
  if (!f || !(f->theorem_mask & function_class::TH_REL_APX_ABS)) return NULL;
  return new relative_error_from_approx_abs_scheme(real, predicated_real(real.real(), PRED_ABS), f);
}

// ROUNDING_BOUND
REGISTER_SCHEME_BEGIN(rounding_bound);
  function_class const *function;
  rounding_bound_scheme(ast_real const *r, ast_real const *rr, function_class const *f)
    : proof_scheme(predicated_real(r, PRED_BND), one_needed(rr), ""), function(f) {}
REGISTER_SCHEME_END(rounding_bound);

void rounding_bound_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  res.bnd() = function->round(hyps[0].bnd(), name);
}

proof_scheme *rounding_bound_scheme::factory(ast_real const *real)
{
  real_op const *p = boost::get < real_op const >(real);
  if (!p || !p->fun || !(p->fun->theorem_mask & function_class::TH_RND)) return NULL;
  return new rounding_bound_scheme(real, unround(p->fun->type, p->ops), p->fun);
}

// ENFORCE_BOUND
REGISTER_SCHEME_BEGIN(enforce_bound);
  function_class const *function;
  enforce_bound_scheme(ast_real const *r, function_class const *f)
    : proof_scheme(predicated_real(r, PRED_BND), one_needed(r), ""), function(f) {}
REGISTER_SCHEME_END(enforce_bound);

void enforce_bound_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  res.bnd() = function->enforce(hyps[0].bnd(), name);
}

proof_scheme *enforce_bound_scheme::factory(ast_real const *real)
{
  real_op const *p = boost::get < real_op const >(real);
  if (!p || !p->fun || !(p->fun->theorem_mask & function_class::TH_ENF)) return NULL;
  return new enforce_bound_scheme(real, p->fun);
}

// SUB_OF_EQL
REGISTER_SCHEME_BEGIN(sub_of_eql);
  sub_of_eql_scheme(predicated_real const &r, predicated_real const &n)
    : proof_scheme(r, preal_vect(1, n), "sub_of_eql", UPD_TRIV) {}
REGISTER_SCHEME_END_PATTERN(sub_of_eql, predicated_real(pattern(0) - pattern(1), PRED_BND));

void sub_of_eql_scheme::compute(property const hyps[], property &res, std::string &) const
{
  res.bnd() = zero();
}

proof_scheme *sub_of_eql_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  if (holders[0] == holders[1] || is_constant(real.real())) return NULL;
  return new sub_of_eql_scheme(real, predicated_real(holders[0], holders[1], PRED_EQL));
}

// EQL_OF_CST
REGISTER_SCHEME_BEGIN(eql_of_cst);
  eql_of_cst_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r, v, "eql_of_cst") {}
REGISTER_SCHEME_END_PREDICATE(eql_of_cst);

void eql_of_cst_scheme::compute(property const hyps[], property &res, std::string &) const
{
  if (!is_singleton(hyps[1].bnd()) || !(hyps[0].bnd() <= hyps[1].bnd())) res = property();
}

proof_scheme *eql_of_cst_scheme::factory(predicated_real const &real)
{
  if (real.pred() != PRED_EQL ||
      !is_constant(real.real()) || !is_constant(real.real2())) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(real.real(), PRED_BND));
  hyps.push_back(predicated_real(real.real2(), PRED_BND));
  return new eql_of_cst_scheme(real, hyps);
}

// REL_REFL
REGISTER_SCHEME_BEGIN(rel_refl);
  rel_refl_scheme(predicated_real const &r)
    : proof_scheme(r, preal_vect(), "rel_refl", UPD_TRIV) {}
REGISTER_SCHEME_END_PATTERN(rel_refl, predicated_real(pattern(0), pattern(0), PRED_REL));

void rel_refl_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  res.bnd() = zero();
}

proof_scheme *rel_refl_scheme::factory(predicated_real const &real, ast_real_vect const &)
{
  return new rel_refl_scheme(real);
}

// EQL_TRANS
REGISTER_SCHEME_BEGIN(eql_trans);
  eql_trans_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r, v, "eql_trans") {}
 public:
  static proof_scheme *factory2(predicated_real const &, ast_real_vect const &);
REGISTER_SCHEME_END_PATTERN(eql_trans, predicated_real(pattern(1), pattern(2), PRED_EQL));

void eql_trans_scheme::compute(property const hyps[], property &res, std::string &) const
{
}

proof_scheme *eql_trans_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  if (holders[0] == holders[2]) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[1], holders[0], PRED_EQL));
  hyps.push_back(predicated_real(holders[0], holders[2], PRED_EQL));
  return new eql_trans_scheme(real, hyps);
}

proof_scheme *eql_trans_scheme::factory2(predicated_real const &real, ast_real_vect const &holders)
{
  if (holders[1] == holders[2]) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[2], holders[1], PRED_EQL));
  hyps.push_back(predicated_real(holders[1], holders[0], PRED_EQL));
  return new eql_trans_scheme(real, hyps);
}

static factory_creator eql_trans_scheme_register2(&eql_trans_scheme::factory2,
  predicated_real(pattern(2), pattern(0), PRED_EQL));

// COMPUTATION
REGISTER_SCHEME_BEGIN(computation);
  real_op const *naked_real;
  computation_scheme(ast_real const *r1, real_op const *r2, preal_vect const &v, char const *n)
    : proof_scheme(predicated_real(r1, PRED_BND), v, n), naked_real(r2) {}
REGISTER_SCHEME_END(computation);


void computation_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  real_op const *r = naked_real;
  switch (r->ops.size()) {
  case 1: {
    interval const &i = hyps[0].bnd();
    switch (r->type) {
    case UOP_NEG:
      res.bnd() = -i;
      return;
    case UOP_SQRT:
      if (lower(i) < 0) return;
      res.bnd() = sqrt(i);
      return;
#if 0
    case UOP_ABS:
      return create_theorem(1, &res, property(real, abs(i)), std::string("abs_") += ('o' + sign(i)), &abs_updater);
#endif
    case UOP_LOG:
      if (lower(i) <= 0) return;
      res.bnd() = log(i);
	  return;
    case UOP_EXP:
      res.bnd() = exp(i);
	  return;
    case UOP_LOG2:
      if (lower(i) <= 0) return;
      res.bnd() = log2(i);
	  return;
    case UOP_EXP2:
      res.bnd() = exp2(i);
	  return;
    default:
      assert(false);
    }
    break; }
  case 2: {
    bool same_ops = r->ops[0] == r->ops[1];
    if (same_ops) {
      if (r->type == BOP_SUB) { res.bnd() = zero(); return; }
      if (r->type == BOP_DIV) {
        number one(1);
        res.bnd() = interval(one, one);
        return;
      }
    }
    interval const &i1 = hyps[0].bnd();
    if (same_ops && r->type == BOP_MUL) {
      res.bnd() = square(i1);
      return;
    }
    interval const &i2 = hyps[1].bnd();
    switch (r->type) {
    case BOP_ADD: res.bnd() = i1 + i2; return;
    case BOP_SUB: res.bnd() = i1 - i2; return;
    case BOP_MUL:
      res.bnd() = i1 * i2;
      name = "mul_xx";
      name[name.size() - 2] = 'o' + sign(i1);
      name[name.size() - 1] = 'o' + sign(i2);
      return;
    case BOP_DIV:
      if (contains_zero(i2)) return;
      res.bnd() = i1 / i2;
      name = "div_xx";
      name[name.size() - 2] = 'o' + sign(i1);
      name[name.size() - 1] = 'o' + sign(i2);
      return;
    default:
      assert(false);
    } }
  default:
    assert(false);
  }
}

proof_scheme *computation_scheme::factory(ast_real const *real)
{
  ast_real const *r = real;
  if (hidden_real const *h = boost::get< hidden_real const >(real))
    r = h->real;
  real_op const *p = boost::get< real_op const >(r);
  if (!p || p->fun || p->type == UOP_ABS) return NULL;
  ast_real_vect const &ops = p->ops;
  preal_vect needed;
  char const *name = "";
  if (ops.size() != 2 || ops[0] != ops[1]) {
    generic:
    needed.reserve(ops.size());
    for (ast_real_vect::const_iterator i = ops.begin(), i_end = ops.end();
         i != i_end; ++i)
      needed.push_back(predicated_real(*i, PRED_BND));
    switch (p->type) {
    case UOP_NEG: name = "neg"; break;
    case UOP_ABS: name = "abs"; break;
    case UOP_SQRT: name = "sqrt"; break;
    case BOP_ADD: name = "add"; break;
    case BOP_SUB: name = "sub"; break;
    default: break;
    }
  } else {
    switch (p->type) {
    case BOP_SUB: name = "sub_refl"; break;
    case BOP_DIV: name = "div_refl"; needed.push_back(predicated_real(ops[0], PRED_NZR)); break;
    case BOP_MUL: name = "square"; needed.push_back(predicated_real(ops[0], PRED_ABS)); break;
    default: goto generic;
    }
  }
  return new computation_scheme(real, p, needed, name);
}

// COMPUTATION_ABS
REGISTER_SCHEME_BEGIN(computation_abs);
  computation_abs_scheme(predicated_real const &r, preal_vect const &v, char const *n, update u)
    : proof_scheme(r, v, n, u) {}
REGISTER_SCHEME_END_PREDICATE(computation_abs);

void computation_abs_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  real_op const *r = boost::get< real_op const >(real.real());
  assert(r);
  interval &i = res.bnd();
  switch (r->ops.size()) {
  case 1:
    i = hyps[0].bnd();
    return;
  case 2: {
    interval const &i1 = hyps[0].bnd();
    interval const &i2 = hyps[1].bnd();
    switch (r->type) {
    case BOP_ADD:
    case BOP_SUB:
      i = interval(lower(abs(i1 - i2)), upper(i1 + i2));
      name = r->type == BOP_ADD ? "add_aa_x" : "sub_aa_x";
      name[name.size() - 1] = lower(i) > 0 ? (lower(i1) > upper(i2) ? 'p' : 'n') : 'o';
      return;
    case BOP_MUL:
      i = i1 * i2;
      return;
    case BOP_DIV:
      if (contains_zero(i2)) return;
      i = i1 / i2;
      return;
    default:
      assert(false);
    } }
  default:
    assert(false);
  }
}

proof_scheme *computation_abs_scheme::factory(predicated_real const &real)
{
  if (real.pred() != PRED_ABS) return NULL;
  real_op const *p = boost::get< real_op const >(real.real());
  if (!p || p->fun || p->type == UOP_SQRT || p->type == UOP_EXP || p->type == UOP_LOG || 
      p->type == UOP_LOG2 || p->type == UOP_EXP2) return NULL;
  if (is_constant(real.real())) return NULL;
  preal_vect needed;
  needed.reserve(p->ops.size());
  for (ast_real_vect::const_iterator i = p->ops.begin(), i_end = p->ops.end();
       i != i_end; ++i)
    needed.push_back(predicated_real(*i, PRED_ABS));
  char const *name = "";
  update upd = UPD_SEEK;
  switch (p->type) {
  case UOP_NEG: name = "neg_a"; upd = UPD_COPY; break;
  case UOP_ABS: name = "abs_a"; upd = UPD_COPY; break;
  case BOP_MUL: name = "mul_aa"; break;
  case BOP_DIV: name = "div_aa"; break;
  default: break;
  }
  return new computation_abs_scheme(real, needed, name, upd);
}

// BND_OF_ABS
REGISTER_SCHEME_BEGIN(bnd_of_abs);
  bnd_of_abs_scheme(ast_real const *r)
    : proof_scheme(predicated_real(r, PRED_BND), preal_vect(1, predicated_real(r, PRED_ABS)), "bnd_of_abs") {}
REGISTER_SCHEME_END(bnd_of_abs);

void bnd_of_abs_scheme::compute(property const hyps[], property &res, std::string &) const
{
  number const &num = upper(hyps[0].bnd());
  res.bnd() = interval(-num, num);
}

proof_scheme *bnd_of_abs_scheme::factory(ast_real const *real)
{
  if (is_hidden(real) || is_constant(real)) return NULL;
  real_op const *p = boost::get< real_op const >(real);
  if (p && p->type == UOP_ABS) return NULL;
  return new bnd_of_abs_scheme(real);
}

// ABS_OF_BND
REGISTER_SCHEME_BEGIN(abs_of_bnd);
  abs_of_bnd_scheme(predicated_real const &r)
    : proof_scheme(r, one_needed(r.real()), "") {}
REGISTER_SCHEME_END_PREDICATE(abs_of_bnd);

void abs_of_bnd_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  interval const &i = hyps[0].bnd();
  res.bnd() = abs(i);
  name = "abs_of_bnd_x";
  name[name.size() - 1] = 'o' + sign(i);
}

proof_scheme *abs_of_bnd_scheme::factory(predicated_real const &real)
{
  if (real.pred() != PRED_ABS) return NULL;
  real_op const *p = boost::get< real_op const >(real.real());
  if (p && p->type == UOP_ABS) return NULL;
  return new abs_of_bnd_scheme(real);
}

// BND_OF_BND_ABS
REGISTER_SCHEME_BEGIN(bnd_of_bnd_abs);
  bnd_of_bnd_abs_scheme(preal_vect const &v) : proof_scheme(v[0], v, "") {}
REGISTER_SCHEME_END(bnd_of_bnd_abs);

void bnd_of_bnd_abs_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  interval const &ib = hyps[0].bnd(), &ia = hyps[1].bnd();
  number const &iba = lower(ib), &ibb = upper(ib), &iab = lower(ia), &iaa = -iab;
  bool b1 = iba <= iaa, b2 = iab <= ibb;
  if (b1 && b2) return;
  res.bnd() = b1 ? interval(iba, iaa) : interval(iab, b2 ? ibb : iab);
  name = b1 ? "bnd_of_bnd_abs_n" : "bnd_of_bnd_abs_p";
}

proof_scheme *bnd_of_bnd_abs_scheme::factory(ast_real const *real)
{
  if (is_hidden(real) || is_constant(real)) return NULL;
  real_op const *p = boost::get< real_op const >(real);
  if (p && p->type == UOP_ABS) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(real, PRED_BND));
  hyps.push_back(predicated_real(real, PRED_ABS));
  return new bnd_of_bnd_abs_scheme(hyps);
}

// UABS_OF_ABS
REGISTER_SCHEME_BEGIN(uabs_of_abs);
  uabs_of_abs_scheme(ast_real const *r, predicated_real const &v)
    : proof_scheme(predicated_real(r, PRED_BND), preal_vect(1, v), "uabs_of_abs", UPD_COPY) {}
REGISTER_SCHEME_END(uabs_of_abs);

void uabs_of_abs_scheme::compute(property const hyps[], property &res, std::string &) const
{
  res.bnd() = hyps[0].bnd();
}

proof_scheme *uabs_of_abs_scheme::factory(ast_real const *real)
{
  real_op const *p = boost::get< real_op const >(real);
  if (!p || p->type != UOP_ABS) return NULL;
  return new uabs_of_abs_scheme(real, predicated_real(p->ops[0], PRED_ABS));
}

// ABS_OF_UABS
REGISTER_SCHEME_BEGIN(abs_of_uabs);
  abs_of_uabs_scheme(predicated_real const &r, predicated_real const &v)
    : proof_scheme(r, preal_vect(1, v), "abs_of_uabs", UPD_COPY) {}
REGISTER_SCHEME_END_PREDICATE(abs_of_uabs);

void abs_of_uabs_scheme::compute(property const hyps[], property &res, std::string &) const
{
  if (lower(hyps[0].bnd()) < 0) return;
  res.bnd() = hyps[0].bnd();
}

proof_scheme *abs_of_uabs_scheme::factory(predicated_real const &real)
{
  if (real.pred() != PRED_ABS) return NULL;
  ast_real const *r = real.real();
  if (is_constant(r)) return NULL;
  real_op const *p = boost::get< real_op const >(r);
  if (p && p->type == UOP_ABS) return NULL;
  ast_real const *ra = normalize(ast_real(real_op(UOP_ABS, r)));
  return new abs_of_uabs_scheme(real, predicated_real(ra, PRED_BND));
}

// NUMBER
REGISTER_SCHEME_BEGIN(number);
  number_scheme(ast_real const *r, char const *n)
    : proof_scheme(predicated_real(r, PRED_BND), preal_vect(), n, UPD_TRIV) {}
REGISTER_SCHEME_END(number);

interval create_interval(ast_number const *, ast_number const *, bool widen = true);

void number_scheme::compute(property const[], property &res, std::string &) const
{
  ast_number const *const *r = boost::get< ast_number const *const >(real.real());
  assert(r);
  res.bnd() = create_interval(*r, *r);
}

proof_scheme *number_scheme::factory(ast_real const *real)
{
  ast_number const *const *r = boost::get< ast_number const *const >(real);
  if (!r) return NULL;
  char const *s;
  if ((**r).base == 0 || (**r).exponent == 0) s = "constant1";
  else if ((**r).base == 2) s = "constant2";
  else s = "constant10";
  return new number_scheme(real, s);
}

// NEG_ABS_FIX_FLT
REGISTER_SCHEME_BEGIN(neg_abs_fix_flt);
  neg_abs_fix_flt_scheme(predicated_real const &r, predicated_real const &v, char const *n)
    : proof_scheme(r, preal_vect(1, v), n) {}
REGISTER_SCHEME_END_PREDICATE(neg_abs_fix_flt);

void neg_abs_fix_flt_scheme::compute(property const hyps[], property &res, std::string &) const
{
  res.cst() = hyps[0].cst();
}

proof_scheme *neg_abs_fix_flt_scheme::factory(predicated_real const &real)
{
  predicate_type t = real.pred();
  if (t != PRED_FIX && t != PRED_FLT) return NULL;
  real_op const *p = boost::get< real_op const >(real.real());
  if (!p || (p->type != UOP_ABS && p->type != UOP_NEG)) return NULL;
  std::string name = p->type == UOP_ABS ? "abs_" : "neg_";
  if (is_constant(p->ops[0])) return NULL;
  return new neg_abs_fix_flt_scheme(real, predicated_real(p->ops[0], t), (name + (t == PRED_FIX ? "fix" : "flt")).c_str());
}

// ADD_SUB_FIX
REGISTER_SCHEME_BEGIN(add_sub_fix);
  add_sub_fix_scheme(predicated_real const &r, preal_vect const &v, char const *n)
    : proof_scheme(r, v, n) {}
REGISTER_SCHEME_END_PREDICATE(add_sub_fix);

void add_sub_fix_scheme::compute(property const hyps[], property &res, std::string &) const
{
  res.cst() = std::min(hyps[0].cst(), hyps[1].cst());
}

proof_scheme *add_sub_fix_scheme::factory(predicated_real const &real)
{
  if (real.pred() != PRED_FIX) return NULL;
  real_op const *p = boost::get< real_op const >(real.real());
  if (!p || (p->type != BOP_ADD && p->type != BOP_SUB)) return NULL;
  if (is_constant(p->ops[0]) && is_constant(p->ops[1])) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(p->ops[0], PRED_FIX));
  hyps.push_back(predicated_real(p->ops[1], PRED_FIX));
  return new add_sub_fix_scheme(real, hyps, p->type == BOP_SUB ? "sub_fix" : "add_fix");
}

// SUB_FLT
REGISTER_SCHEME_BEGIN(sub_flt);
  sub_flt_scheme(predicated_real const &r, preal_vect const &v, char const *n)
    : proof_scheme(r, v, n) {}
REGISTER_SCHEME_END_PATTERN(sub_flt, predicated_real(pattern(0) - pattern(1), PRED_FLT));

void sub_flt_scheme::compute(property const hyps[], property &res, std::string &) const
{
  static interval r(-0.5, 1);
  if (!(hyps[2].bnd() <= r)) return;
  res.cst() = std::max(hyps[0].cst(), hyps[1].cst());
}

proof_scheme *sub_flt_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  if (holders[0] == holders[1]) return NULL;
  if (is_constant(holders[0]) && is_constant(holders[1])) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[0], PRED_FLT));
  hyps.push_back(predicated_real(holders[1], PRED_FLT));
  hyps.push_back(predicated_real(holders[0], holders[1], PRED_REL));
  char const *name = "sub_flt";
  real_op const *r = boost::get< real_op const >(real.real());
  assert(r && r->type == BOP_SUB);
  if (r->ops[0] == holders[1]) name = "sub_flt_rev";
  return new sub_flt_scheme(real, hyps, name);
}

static factory_creator sub_flt_scheme_register2(&sub_flt_scheme::factory,
  predicated_real(pattern(1) - pattern(0), PRED_FLT));

// MUL_FIX_FLT
REGISTER_SCHEME_BEGIN(mul_fix_flt);
  mul_fix_flt_scheme(predicated_real const &r, preal_vect const &v, char const *n)
    : proof_scheme(r, v, n) {}
REGISTER_SCHEME_END_PREDICATE(mul_fix_flt);

void mul_fix_flt_scheme::compute(property const hyps[], property &res, std::string &) const
{
  res.cst() = hyps[0].cst() + hyps[1].cst();
}

proof_scheme *mul_fix_flt_scheme::factory(predicated_real const &real)
{
  predicate_type t = real.pred();
  if (t != PRED_FIX && t != PRED_FLT) return NULL;
  real_op const *p = boost::get< real_op const >(real.real());
  if (!p || p->type != BOP_MUL) return NULL;
  if (is_constant(p->ops[0]) && is_constant(p->ops[1])) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(p->ops[0], t));
  hyps.push_back(predicated_real(p->ops[1], t));
  return new mul_fix_flt_scheme(real, hyps, t == PRED_FIX ? "mul_fix" : "mul_flt");
}

// FIX_OF_FLT_BND
REGISTER_SCHEME_BEGIN(fix_of_flt_bnd);
  fix_of_flt_bnd_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r, v, "fix_of_flt_bnd") {}
REGISTER_SCHEME_END_PREDICATE(fix_of_flt_bnd);

void fix_of_flt_bnd_scheme::compute(property const hyps[], property &res, std::string &) const
{
  mpz_t m;
  mpz_init(m);
  int e, s;
  split_exact(lower(hyps[1].bnd()).data->val, m, e, s);
  if (s <= 0) { mpz_clear(m); res.clear(); return; }
  e += mpz_sizeinbase(m, 2);
  mpz_clear(m);
  res.cst() = e - hyps[0].cst();
}

proof_scheme *fix_of_flt_bnd_scheme::factory(predicated_real const &real)
{
  if (real.pred() != PRED_FIX) return NULL;
  ast_real const *r = real.real();
  if (is_changing_sign(r) || is_constant(r)) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(r, PRED_FLT));
  hyps.push_back(predicated_real(r, PRED_ABS));
  return new fix_of_flt_bnd_scheme(real, hyps);
}

// FLT_OF_FIX_BND
REGISTER_SCHEME_BEGIN(flt_of_fix_bnd);
  flt_of_fix_bnd_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r, v, "flt_of_fix_bnd") {}
REGISTER_SCHEME_END_PREDICATE(flt_of_fix_bnd);

void flt_of_fix_bnd_scheme::compute(property const hyps[], property &res, std::string &) const
{
  mpz_t m;
  mpz_init(m);
  int e, s;
  split_exact(upper(hyps[1].bnd()).data->val, m, e, s);
  if (s <= 0) { mpz_clear(m); res.clear(); return; }
  e += mpz_sizeinbase(m, 2);
  mpz_clear(m);
  res.cst() = e - hyps[0].cst();
}

proof_scheme *flt_of_fix_bnd_scheme::factory(predicated_real const &real)
{
  if (real.pred() != PRED_FLT) return NULL;
  ast_real const *r = real.real();
  if (is_changing_sign(r) || is_constant(r)) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(r, PRED_FIX));
  hyps.push_back(predicated_real(r, PRED_ABS));
  return new flt_of_fix_bnd_scheme(real, hyps);
}

// FIX_OF_SINGLETON_BND
REGISTER_SCHEME_BEGIN(fix_of_singleton_bnd);
  fix_of_singleton_bnd_scheme(predicated_real const &r, predicated_real const &v)
    : proof_scheme(r, preal_vect(1, v), "fix_of_singleton_bnd") {}
REGISTER_SCHEME_END_PREDICATE(fix_of_singleton_bnd);

void fix_of_singleton_bnd_scheme::compute(property const hyps[], property &res, std::string &) const
{
  interval const &i = hyps[0].bnd();
  number const &l = lower(i);
  if (upper(i) != l) { res.clear(); return; }
  mpz_t m;
  mpz_init(m);
  int e, s;
  split_exact(l.data->val, m, e, s);
  mpz_clear(m);
  if (s == 0) { res.clear(); return; }
  res.cst() = e;
}

proof_scheme *fix_of_singleton_bnd_scheme::factory(predicated_real const &real)
{
  if (real.pred() != PRED_FIX) return NULL;
  return new fix_of_singleton_bnd_scheme(real, predicated_real(real.real(), PRED_ABS));
}

// FLT_OF_SINGLETON_BND
REGISTER_SCHEME_BEGIN(flt_of_singleton_bnd);
  flt_of_singleton_bnd_scheme(predicated_real const &r, predicated_real const &v)
    : proof_scheme(r, preal_vect(1, v), "flt_of_singleton_bnd") {}
REGISTER_SCHEME_END_PREDICATE(flt_of_singleton_bnd);

void flt_of_singleton_bnd_scheme::compute(property const hyps[], property &res, std::string &) const
{
  interval const &i = hyps[0].bnd();
  number const &l = lower(i);
  if (upper(i) != l) { res.clear(); return; }
  mpz_t m;
  mpz_init(m);
  int e, s;
  split_exact(l.data->val, m, e, s);
  if (s == 0) e = 0;
  else e = mpz_sizeinbase(m, 2);
  mpz_clear(m);
  res.cst() = e;
}

proof_scheme *flt_of_singleton_bnd_scheme::factory(predicated_real const &real)
{
  if (real.pred() != PRED_FLT) return NULL;
  return new flt_of_singleton_bnd_scheme(real, predicated_real(real.real(), PRED_ABS));
}

// BND_OF_NZR_REL
REGISTER_SCHEME_BEGIN(bnd_of_nzr_rel);
  bnd_of_nzr_rel_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r, v, "bnd_of_nzr_rel", UPD_COPY) {}
REGISTER_SCHEME_END_PATTERN(bnd_of_nzr_rel,
  predicated_real((pattern(1) - pattern(0)) / pattern(0), PRED_BND));

void bnd_of_nzr_rel_scheme::compute(property const hyps[], property &res, std::string &) const
{
  res.bnd() = hyps[1].bnd();
}

proof_scheme *bnd_of_nzr_rel_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  if (holders[0] == holders[1]) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[0], PRED_NZR));
  hyps.push_back(predicated_real(holders[1], holders[0], PRED_REL));
  return new bnd_of_nzr_rel_scheme(real, hyps);
}

// REL_OF_NZR_BND
REGISTER_SCHEME_BEGIN(rel_of_nzr_bnd);
  rel_of_nzr_bnd_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r, v, "rel_of_nzr_bnd", UPD_COPY) {}
REGISTER_SCHEME_END_PREDICATE(rel_of_nzr_bnd);

void rel_of_nzr_bnd_scheme::compute(property const hyps[], property &res, std::string &) const
{
  if (lower(hyps[1].bnd()) <= -1) return;
  res.bnd() = hyps[1].bnd();
}

proof_scheme *rel_of_nzr_bnd_scheme::factory(predicated_real const &real)
{
  if (real.pred() != PRED_REL) return NULL;
  ast_real const *r1 = real.real(), *r2 = real.real2();
  if (r1 == r2) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(r2, PRED_NZR));
  hyps.push_back(predicated_real(normalize(real_op(
    normalize(real_op(r1, BOP_SUB, r2)), BOP_DIV, r2)), PRED_BND));
  return new rel_of_nzr_bnd_scheme(real, hyps);
}

// COMPUTATION_REL_ADD
REGISTER_SCHEME_BEGIN(computation_rel_add);
  computation_rel_add_scheme(predicated_real const &r, preal_vect const &v, char const *n)
    : proof_scheme(r, v, n) {}
REGISTER_SCHEME_END_PREDICATE(computation_rel_add);

void computation_rel_add_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  res.bnd() = add_relative(hyps[0].bnd(), hyps[1].bnd(), hyps[2].bnd());
}

proof_scheme *computation_rel_add_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_REL) return NULL;
  real_op const *p = boost::get< real_op const >(real.real());
  if (!p || (p->type != BOP_ADD && p->type != BOP_SUB)) return NULL;
  ast_real const *r2 = real.real2();
  real_op const *p2 = boost::get< real_op const >(r2);
  if (!p2 || p->type != p2->type) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(p->ops[0], p2->ops[0], PRED_REL));
  hyps.push_back(predicated_real(p->ops[1], p2->ops[1], PRED_REL));
  hyps.push_back(predicated_real(normalize(real_op(p2->ops[0], BOP_DIV, r2)), PRED_BND));
  hyps.push_back(predicated_real(r2, PRED_NZR));
  return new computation_rel_add_scheme(real, hyps, p->type == BOP_SUB ? "sub_rr" : "add_rr");
}

// COMPUTATION_REL_MUL
REGISTER_SCHEME_BEGIN(computation_rel_mul);
  computation_rel_mul_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r, v, "mul_rr") {}
REGISTER_SCHEME_END_PATTERN(computation_rel_mul,
  predicated_real(pattern(0) * pattern(1), pattern(2) * pattern(3), PRED_REL));

void computation_rel_mul_scheme::compute(property const hyps[], property &res, std::string &) const
{
  res.bnd() = compose_relative(hyps[0].bnd(), hyps[1].bnd());
}

proof_scheme *computation_rel_mul_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  if (holders[0] == holders[2] || holders[1] == holders[3]) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[0], holders[2], PRED_REL));
  hyps.push_back(predicated_real(holders[1], holders[3], PRED_REL));
  return new computation_rel_mul_scheme(real, hyps);
}

// COMPUTATION_REL_DIV
REGISTER_SCHEME_BEGIN(computation_rel_div);
  computation_rel_div_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r, v, "div_rr") {}
REGISTER_SCHEME_END_PATTERN(computation_rel_div,
  predicated_real(pattern(0) / pattern(1), pattern(2) / pattern(3), PRED_REL));

void computation_rel_div_scheme::compute(property const hyps[], property &res, std::string &) const
{
  res.bnd() = compose_relative_inv(hyps[0].bnd(), hyps[1].bnd());
}

proof_scheme *computation_rel_div_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  if (holders[0] == holders[2] || holders[1] == holders[3]) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[0], holders[2], PRED_REL));
  hyps.push_back(predicated_real(holders[1], holders[3], PRED_REL));
  hyps.push_back(predicated_real(holders[3], PRED_NZR));
  return new computation_rel_div_scheme(real, hyps);
}

// COMPUTATION_REL_INV
REGISTER_SCHEME_BEGIN(computation_rel_inv);
  computation_rel_inv_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r, v, "inv_r") {}
REGISTER_SCHEME_END_PATTERN(computation_rel_inv,
  predicated_real(pattern(0) / pattern(1), pattern(0) / pattern(2), PRED_REL));

void computation_rel_inv_scheme::compute(property const hyps[], property &res, std::string &) const
{
  res.bnd() = compose_relative_inv(zero(), hyps[0].bnd());
}

proof_scheme *computation_rel_inv_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  if (holders[1] == holders[2]) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[1], holders[2], PRED_REL));
  hyps.push_back(predicated_real(holders[2], PRED_NZR));
  return new computation_rel_inv_scheme(real, hyps);
}

// COMPOSE_REL
REGISTER_SCHEME_BEGIN(compose_rel);
  compose_rel_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r, v, "compose") {}
 public:
  static proof_scheme *factory2(predicated_real const &, ast_real_vect const &);
REGISTER_SCHEME_END_PATTERN(compose_rel, predicated_real(pattern(1), pattern(2), PRED_REL));

void compose_rel_scheme::compute(property const hyps[], property &res, std::string &) const
{
  res.bnd() = compose_relative(hyps[0].bnd(), hyps[1].bnd());
}

proof_scheme *compose_rel_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  if (holders[0] == holders[2]) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[1], holders[0], PRED_REL));
  hyps.push_back(predicated_real(holders[0], holders[2], PRED_REL));
  return new compose_rel_scheme(real, hyps);
}

proof_scheme *compose_rel_scheme::factory2(predicated_real const &real, ast_real_vect const &holders)
{
  if (holders[1] == holders[2]) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[2], holders[1], PRED_REL));
  hyps.push_back(predicated_real(holders[1], holders[0], PRED_REL));
  return new compose_rel_scheme(real, hyps);
}

static factory_creator compose_rel_scheme_register2(&compose_rel_scheme::factory2,
  predicated_real(pattern(2), pattern(0), PRED_REL));

// COMPOSE_REL_SWAP
REGISTER_SCHEME_BEGIN(compose_rel_swap);
  compose_rel_swap_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r, v, "compose_swap") {}
REGISTER_SCHEME_END_PATTERN(compose_rel_swap,
  predicated_real(pattern(2) * pattern(1), pattern(3), PRED_REL));

void compose_rel_swap_scheme::compute(property const hyps[], property &res, std::string &) const
{
  res.bnd() = compose_relative(hyps[0].bnd(), hyps[1].bnd());
}

proof_scheme *compose_rel_swap_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  static ast_real const *one = normalize(token_one);
  real_op const *p = boost::get<real_op const>(holders[0]);
  if (!p || p->type != BOP_DIV || p->ops[0] != one) return NULL;
  ast_real const *r = normalize(real_op(holders[3], BOP_MUL, p->ops[1]));
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[2], r, PRED_REL));
  hyps.push_back(predicated_real(holders[1], holders[0], PRED_REL));
  hyps.push_back(predicated_real(p->ops[1], PRED_NZR));
  return new compose_rel_swap_scheme(real, hyps);
}

// ERROR_OF_REL
REGISTER_SCHEME_BEGIN(error_of_rel);
  error_of_rel_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r, v, "") {}
REGISTER_SCHEME_END_PATTERN(error_of_rel, predicated_real(pattern(1) - pattern(0), PRED_BND));

void error_of_rel_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  interval const &i1 = hyps[0].bnd(), &i2 = hyps[1].bnd();
  res.bnd() = i1 * i2;
  name = "error_of_rel_xx";
  name[name.size() - 2] = 'o' + sign(i1);
  name[name.size() - 1] = 'o' + sign(i2);
}

proof_scheme *error_of_rel_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  if (holders[0] == holders[1]) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[1], holders[0], PRED_REL));
  hyps.push_back(predicated_real(holders[0], PRED_BND));
  return new error_of_rel_scheme(real, hyps);
}

// BND_OF_BND_REL
REGISTER_SCHEME_BEGIN(bnd_of_bnd_rel);
  bnd_of_bnd_rel_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r, v, "") {}
REGISTER_SCHEME_END_PATTERN(bnd_of_bnd_rel, predicated_real(pattern(1), PRED_BND));

void bnd_of_bnd_rel_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  interval const &i1 = hyps[0].bnd(), &i2 = hyps[1].bnd();
  res.bnd() = i1 * (interval(1, 1) + i2);
  name = "bnd_of_bnd_rel_x";
  name[name.size() - 1] = 'o' + sign(i1);
}

proof_scheme *bnd_of_bnd_rel_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  if (holders[0] == holders[1]) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[0], PRED_BND));
  hyps.push_back(predicated_real(holders[1], holders[0], PRED_REL));
  return new bnd_of_bnd_rel_scheme(real, hyps);
}

// BND_OF_REL_BND
REGISTER_SCHEME_BEGIN(bnd_of_rel_bnd);
  bnd_of_rel_bnd_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r, v, "") {}
REGISTER_SCHEME_END_PATTERN(bnd_of_rel_bnd, predicated_real(pattern(-1), PRED_BND));

void bnd_of_rel_bnd_scheme::compute(property const hyps[], property &res, std::string &name) const
{
  interval const &i1 = hyps[0].bnd(), &i2 = hyps[1].bnd();
  interval i = interval(1, 1) + i2;
  if (contains_zero(i)) return;
  res.bnd() = i1 / i;
  name = "bnd_of_rel_bnd_x";
  name[name.size() - 1] = 'o' + sign(i1);
}

proof_scheme *bnd_of_rel_bnd_scheme::factory(predicated_real const &real,
  ast_real_vect const &holders)
{
  if (holders[0] == holders[1]) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[1], PRED_BND));
  hyps.push_back(predicated_real(holders[1], holders[0], PRED_REL));
  return new bnd_of_rel_bnd_scheme(real, hyps);
}

// NEG_NZR
REGISTER_SCHEME_BEGIN(neg_nzr);
  neg_nzr_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r, v, "neg_nzr") {}
REGISTER_SCHEME_END_PATTERN(neg_nzr, predicated_real(-pattern(0), PRED_NZR));

void neg_nzr_scheme::compute(property const[], property &, std::string &) const
{
}

proof_scheme *neg_nzr_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[0], PRED_NZR));
  return new neg_nzr_scheme(real, hyps);
}

// MUL_NZR
REGISTER_SCHEME_BEGIN(mul_nzr);
  mul_nzr_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r, v, "mul_nzr") {}
REGISTER_SCHEME_END_PATTERN(mul_nzr, predicated_real(pattern(0) * pattern(1), PRED_NZR));

void mul_nzr_scheme::compute(property const[], property &, std::string &) const
{
}

proof_scheme *mul_nzr_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[0], PRED_NZR));
  hyps.push_back(predicated_real(holders[1], PRED_NZR));
  return new mul_nzr_scheme(real, hyps);
}

// DIV_NZR
REGISTER_SCHEME_BEGIN(div_nzr);
  div_nzr_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r, v, "div_nzr") {}
REGISTER_SCHEME_END_PATTERN(div_nzr, predicated_real(pattern(0) / pattern(1), PRED_NZR));

void div_nzr_scheme::compute(property const[], property &, std::string &) const
{
}

proof_scheme *div_nzr_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[0], PRED_NZR));
  hyps.push_back(predicated_real(holders[1], PRED_NZR));
  return new div_nzr_scheme(real, hyps);
}

// NZR_OF_ABS
REGISTER_SCHEME_BEGIN(nzr_of_abs);
  nzr_of_abs_scheme(predicated_real const &r, predicated_real const &n)
    : proof_scheme(r, preal_vect(1, n), "nzr_of_abs") {}
REGISTER_SCHEME_END_PREDICATE(nzr_of_abs);

void nzr_of_abs_scheme::compute(property const hyps[], property &res, std::string &) const
{
  if (contains_zero(hyps[0].bnd())) res = property();
}

proof_scheme *nzr_of_abs_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_NZR) return NULL;
  return new nzr_of_abs_scheme(real, predicated_real(real.real(), PRED_ABS));
}

// NZR_OF_UNCONSTRAINED
REGISTER_SCHEME_BEGIN(nzr_of_unconstrained);
  nzr_of_unconstrained_scheme(predicated_real const &r)
    : proof_scheme(r, preal_vect(), "$FALSE") {}
REGISTER_SCHEME_END_PREDICATE(nzr_of_unconstrained);

void nzr_of_unconstrained_scheme::compute(property const[], property &, std::string &) const
{
}

proof_scheme *nzr_of_unconstrained_scheme::factory(predicated_real const &real)
{
  extern bool parameter_constrained;
  if (real.pred() != PRED_NZR || parameter_constrained) return NULL;
  return new nzr_of_unconstrained_scheme(real);
}

// NZR_OF_NZR_REL
REGISTER_SCHEME_BEGIN(nzr_of_nzr_rel);
  nzr_of_nzr_rel_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r, v, "nzr_of_nzr_rel") {}
REGISTER_SCHEME_END_PATTERN(nzr_of_nzr_rel, predicated_real(pattern(1), PRED_NZR));

void nzr_of_nzr_rel_scheme::compute(property const hyps[], property &res, std::string &) const
{
  if (lower(hyps[1].bnd()) <= -1) res.clear();
}

proof_scheme *nzr_of_nzr_rel_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[0], PRED_NZR));
  hyps.push_back(predicated_real(holders[1], holders[0], PRED_REL));
  return new nzr_of_nzr_rel_scheme(real, hyps);
}

// NZR_OF_NZR_REL_REV
REGISTER_SCHEME_BEGIN(nzr_of_nzr_rel_rev);
  nzr_of_nzr_rel_rev_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r, v, "nzr_of_nzr_rel_rev") {}
REGISTER_SCHEME_END_PATTERN(nzr_of_nzr_rel_rev, predicated_real(pattern(-1), PRED_NZR));

void nzr_of_nzr_rel_rev_scheme::compute(property const hyps[], property &res, std::string &) const
{
}

proof_scheme *nzr_of_nzr_rel_rev_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[1], PRED_NZR));
  hyps.push_back(predicated_real(holders[1], holders[0], PRED_REL));
  return new nzr_of_nzr_rel_rev_scheme(real, hyps);
}

// BND_DIV_OF_REL_BND_DIV
REGISTER_SCHEME_BEGIN(bnd_div_of_rel_bnd_div);
  bnd_div_of_rel_bnd_div_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r, v, "bnd_div_of_rel_bnd_div") {}
REGISTER_SCHEME_END_PATTERN(bnd_div_of_rel_bnd_div, predicated_real((pattern(1) - pattern(0)) / pattern(2), PRED_BND));

void bnd_div_of_rel_bnd_div_scheme::compute(property const hyps[], property &res, std::string &) const
{
  res.bnd() = hyps[0].bnd() * hyps[1].bnd();
}

proof_scheme *bnd_div_of_rel_bnd_div_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  preal_vect hyps;
  if (holders[0] == holders[2]) return NULL;
  hyps.push_back(predicated_real(holders[1], holders[0], PRED_REL));
  hyps.push_back(predicated_real(normalize(real_op(holders[0], BOP_DIV, holders[2])), PRED_BND));
  hyps.push_back(predicated_real(holders[2], PRED_NZR));
  return new bnd_div_of_rel_bnd_div_scheme(real, hyps);
}
