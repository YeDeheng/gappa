/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <map>
#include <iostream>
#include <sstream>
#include "backends/backend.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"

extern std::string get_real_split(number const &f, int &exp, bool &zero);

static std::string convert_name(std::string const &name) {
  if (name == "sqrt") return "sqrtG";
  std::string::size_type p2 = name.find(',');
  if (p2 == std::string::npos) return name;
  std::string prefix = name.substr(0, p2);
  std::ostringstream res;
  if (prefix == "rounding_float") {
    std::string::size_type p1;
    p2 = name.find(',', p1 = p2 + 1);
    std::string dir = name.substr(p1, p2 - p1);
    if (dir == "ne") dir = "Nearest";
    else if (dir == "zr") dir = "Zero";
    else if (dir == "up") dir = "Up";
    else if (dir == "dn") dir = "Down";
    p2 = name.find(',', p1 = p2 + 1);
    int prec = std::atoi(name.substr(p1, p2 - p1).c_str());
    p2 = name.find(',', p1 = p2 + 1);
    int exp = std::atoi(name.substr(p1, std::string::npos).c_str());
    res << "round (" << (exp - prec) * 2 + 4 << ',' << prec << ',' << exp << ") " << dir;
    return res.str();
  }
  bool fragile = false;
  res << prefix;
  do {
    std::string::size_type p1 = p2 + 1;
    p2 = name.find(',', p1);
    std::string s(name, p1, p2 == std::string::npos ? p2 : p2 - p1);
    if (!std::isalpha(s[0])) {
      res << " (" << s << ')';
      fragile = true;
    } else res << '_' << s;
  } while (p2 != std::string::npos);
  if (!fragile) return res.str();
  return '(' + res.str() + ')';
}

static id_cache< std::string > displayed_floats;

static std::string display(number const &f) {
  std::ostringstream s;
  bool zero;
  int exp;
  std::string t = get_real_split(f, exp, zero);
  if (zero)
    s << "&0";
  else if (t[0] == '-') {
    t[0] = '&';
    s << "--(" << t << ')';
  } else s << '&' << t;
  if (!zero && exp != 0)
    s << (exp < 0 ? " / &2 pow " : " * &2 pow ") << std::abs(exp);
  std::string const &s_ = s.str();
  int f_id = displayed_floats.find(s_);
  std::string name = composite('f', f_id);
  if (f_id >= 0)
    *out << "NOTATION `(" << name << ":real) = " << s_ << "`;;\n";
  return name;
}

static id_cache< std::string > displayed_intervals;

static std::string display(interval const &i) {
  std::ostringstream s;
  s << display(lower(i)) << ":real),(" << display(upper(i));
  std::string const &s_ = s.str();
  int i_id = displayed_intervals.find(s_);
  std::string name = composite('i', i_id);
  if (i_id >= 0)
    *out << "NOTATION `(" << name << ":real#real) = ((" << s_ << ":real))`;;\n";
  return name;
}

static id_cache< ast_real const * > displayed_reals;

static std::string display(ast_real const *r)
{
  if (hidden_real const *h = boost::get< hidden_real const >(r))
    r = h->real;
  int r_id = displayed_reals.find(r);
  std::string name = r->name ? '_' + r->name->name : composite('r', r_id);
  if (r_id < 0)
    return name;
  if (boost::get< undefined_real const >(r)) {
    *out << "VARIABLE `" << name << ": real`;;\n";
    return name;
  }
  auto_flush plouf;
  plouf << "NOTATION `(" << name << ":real) = ";
  if (ast_number const *const *nn = boost::get< ast_number const *const >(r)) {
    ast_number const &n = **nn;
    if (n.base == 0) plouf << "&0";
    else {
      std::string t = n.mantissa;
      assert(t.size() > 0 && (t[0] == '+' || t[0] == '-'));
      bool neg = t[0] == '-';
      t[0] = '&';
      if (neg) plouf << "--(" << t << ')';
      else plouf << t;
      if (n.exponent != 0)
        plouf << ' ' << (n.exponent < 0 ? '/' : '*') << " &" << n.base << " pow " << std::abs(n.exponent);
    }
  } else if (real_op const *o = boost::get< real_op const >(r)) {
    static char const op[] = "X-XX+-*/XX";
    if (o->type == ROP_FUN) {
      plouf << convert_name(o->fun->description());
      for(ast_real_vect::const_iterator i = o->ops.begin(), end = o->ops.end(); i != end; ++i)
        plouf << " (" << display(*i) << ":real)";
    } else if (o->ops.size() == 1) {
      std::string s(1, op[o->type]);
      switch (o->type) {
      case UOP_NEG: s = "--"; break;
      case UOP_ABS: s = "abs"; break;
      case UOP_SQRT: s = "sqrt"; break;
      default: assert(false);
      }
      plouf << '(' << s << " (" << display(o->ops[0]) << ":real))";
    } else
      plouf << '(' << display(o->ops[0]) << ":real) " << op[o->type] << " (" << display(o->ops[1]) << ":real)";
  } else assert(false);
  plouf << "`;;\n";
  return name;
}

static id_cache< std::string > displayed_properties;

static std::string display(property const &p) {
  std::ostringstream s;
  predicate_type t = p.real.pred();
  ast_real const *real = p.real.real();
  if (p.real.pred_bnd()) {
    interval const &bnd = p.bnd();
    if (lower(bnd) == number::neg_inf) {
      assert(t == PRED_BND);
      s << "((" << display(real) << ":real) <= (" << display(upper(bnd)) << ":real))";
    } else if (upper(bnd) == number::pos_inf) {
      assert(t == PRED_BND);
      s << "((" << display(lower(bnd)) << ":real) <= (" << display(real) << ":real))";
    } else {
      switch (t) {
      case PRED_BND: s << "BND (" << display(real) << ":real) (" << display(bnd) << ":real#real)"; break;
      case PRED_ABS: s << "ABS (" << display(real) << ":real) (" << display(bnd) << ":real#real)"; break;
      case PRED_REL: s << "REL (" << display(real) << ":real) (" << display(p.real.real2())
                       << ":real) (" << display(bnd) << ":real#real)"; break;
      default: assert(false);
      }
    }
  } else {
    switch (t) {
    case PRED_FIX: s << "FIX (" << display(real) << ":real) (" << p.cst() << ')'; break;
    case PRED_FLT: s << "FLT (" << display(real) << ":real) (" << p.cst() << ')'; break;
    case PRED_EQL: s << "EQL (" << display(real) << ":real) (" << display(p.real.real2()) << ":real)"; break;
    case PRED_NZR: s << "NZR (" << display(real) << ":real)"; break;
    default: assert(false);
    }
  }
  std::string s_ = s.str();
  int p_id = displayed_properties.find(s_);
  std::string name = composite('p', p_id);
  if (p_id >= 0)
    *out << "NOTATION `(" << name << ":bool) = " << s_ << "`;; (* " << dump_property(p) << " *)\n";
  return name;
}

static std::string display(node *n);

static std::string display(theorem_node *t) {
  static int t_id = 0;
  std::string name = composite('t', ++t_id);
  auto_flush plouf;
  plouf << "LEMMA \"" << name << "\" `(";
  for(property_vect::const_iterator i = t->hyp.begin(), end = t->hyp.end(); i != end; ++i)
    plouf << display(*i) << ":bool) ==> (";
  plouf << display(t->res) << ":bool)`;;\n";
  int nb_hyps = t->hyp.size();
  if (nb_hyps) {
    plouf << " INTROS [\"h0\"";
    for(int i = 1; i < nb_hyps; ++i) plouf << "; \"h" << i << '"';
    plouf << "];;\n";
  }
  if (std::isdigit(t->name[0]))
    plouf << " APPLY_HYP \"a" << t->name << "\" [";
  else
    plouf << " APPLY " << convert_name(t->name) << " [";
  if (nb_hyps) {
    for(int i = 0; i < nb_hyps; ++i) plouf << (i > 0 ? "; \"h" : "\"h") << i << '"';
  }
  plouf << "] THEN FINALIZE ();;\nQED ();;\n";
  return name;  
}

typedef std::map< predicated_real, std::pair< int, property const * > > property_map;

static std::string subset_name(property const &p1, property const &p2)
{
  assert(p1.implies(p2));
  if (p2.implies(p1)) return std::string();
  char const *prefix = "", *suffix = "";
  switch (p1.real.pred()) {
  case PRED_BND:
    if (lower(p2.bnd()) == number::neg_inf)
      suffix = "_r";
    else if (upper(p2.bnd()) == number::pos_inf)
      suffix = "_l";
    break;
  case PRED_ABS: prefix = "abs_"; break;
  case PRED_REL: prefix = "rel_"; break;
  case PRED_FIX: prefix = "fix_"; break;
  case PRED_FLT: prefix = "flt_"; break;
  case PRED_EQL:
  case PRED_NZR: assert(false);
  }
  return std::string(prefix) + "subset" + suffix;
}

static void invoke_lemma(auto_flush &plouf, property_vect const &hyp, property_map const &pmap) {
  for(property_vect::const_iterator j = hyp.begin(), j_end = hyp.end(); j != j_end; ++j) {
    property_map::const_iterator pki = pmap.find(j->real);
    assert(pki != pmap.end());
    int h = pki->second.first;
    std::string sn = subset_name(*pki->second.second, *j);
    if (sn.empty())
      plouf << " EXACT \"h" << h << "\";;";
    else
      plouf << " APPLY \"" << sn << "\" [\"h" << h << "\"] THEN FINALIZE ();;";
  }
  plouf << '\n';
}

static void invoke_lemma(auto_flush &plouf, node *n, property_map const &pmap) {
  if (n->type != HYPOTHESIS) {
    plouf << " PARTIAL_APPLY \"" << display(n) << "\";;";
    invoke_lemma(plouf, n->graph->get_hypotheses(), pmap);
  } else {
    property_vect hyp;
    hyp.push_back(n->get_result());
    invoke_lemma(plouf, hyp, pmap);
  }
}

static void invoke_subset(auto_flush &plouf, property const p1, property const &p2)
{
  std::string sn = subset_name(p1, p2);
  if (sn.empty()) return;
  plouf << " APPLY \"" << sn << "\" [";
  switch (p1.real.pred()) {
  case PRED_FIX:
  case PRED_FLT: plouf << p1.cst(); break;
  default: plouf << "\"" << display(p1.bnd()) << "\"";
  }
  plouf << "] THEN FINALIZE ();;\n";
}

static id_cache< node * > displayed_nodes;

static std::string display(node *n) {
  assert(n);
  int n_id = displayed_nodes.find(n);
  std::string name = composite('l', n_id);
  if (n_id < 0) return name;
  auto_flush plouf;
  plouf << "LEMMA \"" << name << "\" `";
  property_vect const &n_hyp = n->graph->get_hypotheses();
  property_map pmap;
  plouf << '(';
  int num_hyp = 0;
  for(property_vect::const_iterator i = n_hyp.begin(), end = n_hyp.end();
      i != end; ++i) {
    property const &p = *i;
    plouf << display(p) << ":bool) ==> (";
    pmap.insert(std::make_pair(p.real, std::make_pair(num_hyp++, &p)));
  }
  node_vect const &pred = n->get_subproofs();
  property const &n_res = n->get_result();
  std::string p_res, prefix;
  if (n_res.null()) {
    p_res = "contradiction";
    prefix = "absurd_";
  } else
    p_res = display(n_res);
  plouf << p_res;
  plouf << ":bool)`;; (* " << (!n_res.null() ? dump_property(n_res) : "contradiction") << " *)\n";
  if (num_hyp) {
    plouf << " INTROS [\"h0\"";
    for(int i = 1; i < num_hyp; ++i) plouf << "; \"h" << i << '"';
    plouf << "];;\n";
  }
  switch (n->type) {
  case MODUS: {
    property_map pmap_graph = pmap;
    for(node_vect::const_iterator i = pred.begin(), i_end = pred.end(); i != i_end; ++i) {
      node *m = *i;
      property const &res = m->get_result();
      plouf << " ASSERT \"h" << num_hyp << "\" `(" << display(res) << ":bool)`;;";
      invoke_lemma(plouf, m, pmap_graph);
      pmap[res.real] = std::make_pair(num_hyp++, &res);
    }
    modus_node *mn = dynamic_cast< modus_node * >(n);
    assert(mn && mn->target);
    plouf << " PARTIAL_APPLY \"" << display(mn->target) << "\";;";
    invoke_lemma(plouf, mn->target->hyp, pmap);
    plouf << "QED ();;\n";
    break; }
  case INTERSECTION: {
    int num[2];
    std::string suffix;
    for(int i = 0; i < 2; ++i) {
      node *m = pred[i];
      property const &res = m->get_result();
      switch (res.real.pred()) {
        case PRED_BND:
          if (!is_bounded(res.bnd())) suffix = (i == 0) ? "_hb" : "_bh";
          break;
        case PRED_ABS:
          suffix = "_aa";
          break;
        case PRED_REL:
          suffix = res.real == n_res.real ? "_rr" : "_rr0";
          break;
        default:
          assert(false);
      }
      if (m->type == HYPOTHESIS) {
        property_map::iterator pki = pmap.find(res.real);
        assert(pki != pmap.end());
        num[i] = pki->second.first;
        continue;
      }
      plouf << " ASSERT \"h" << num_hyp << "\" `(" << display(res) << ":bool)`;;";
      invoke_lemma(plouf, m, pmap);
      num[i] = num_hyp++;
    }
    plouf << " APPLY " << prefix << "intersect" << suffix <<
             " [\"h" << num[0] << "\"; \"h" << num[1] << "\"] THEN"
             " FINALIZE ();;\nQED ();;\n";
    break; }
  case UNION: {
    if (false) {
    assert(pred.size() >= 2);
    node *mcase = pred[0];
    property const &pcase = mcase->get_result();
    property_map::mapped_type &hcase = pmap[pcase.real];
    if (mcase->type != HYPOTHESIS) {
      plouf << " assert (h" << num_hyp << " : " << display(pcase) << ").";
      invoke_lemma(plouf, mcase, pmap);
      hcase = std::make_pair(num_hyp, &pcase);
    }
    plouf << " generalize h" << hcase.first << ". clear h" << hcase.first << ".\n";
    for(node_vect::const_iterator i = pred.begin() + 1, i_end = pred.end(); i != i_end; ++i) {
      node *m = *i;
      property_vect const &m_hyp = m->graph->get_hypotheses();
      hcase.second = &m_hyp[0];
      plouf << " assert (u : " << display(m_hyp[0]) << " -> " << p_res << ")."
               " intro h" << hcase.first << ". (* " << m_hyp[0].bnd() << " *)\n";
      property const &res = m->get_result();
      if (!res.null()) // not a contradictory result
        invoke_subset(plouf, res, n_res);
      invoke_lemma(plouf, m, pmap);
      if (i + 1 != i_end)
        plouf << " next_interval (" << prefix << "union) u.\n";
      else
        plouf << " exact u.\n";
    }
    }
    plouf << "QED ();;\n";
    break; }
  case GOAL: {
    node *m = pred[0];
    invoke_subset(plouf, m->get_result(), n_res);
    invoke_lemma(plouf, m, pmap);
    plouf << " FINALIZE ();;\nQED ();;\n";
    break; }
  default:
    assert(false);
  }
  return name;
}

struct holl_backend: backend {
  holl_backend(): backend("holl") {}
  void initialize(std::ostream &o) {
    out = &o;
    o << "(*Require Import Gappa_library.\n"
         "Section Generated_by_Gappa.*)\n";
  }
  void finalize() { *out << "(*End Generated_by_Gappa.*)\n"; }
  virtual std::string rewrite(ast_real const *, ast_real const *, pattern_cond_vect const &);
  virtual std::string theorem(node *n) { return display(n); }
};

std::string holl_backend::rewrite(ast_real const *src, ast_real const *dst,
                                  pattern_cond_vect const &)
{
  static int a_id = 0;
  std::ostringstream name;
  name << ++a_id;
  auto_flush plouf;
  plouf << "HYPOTHESIS \"a" << name.str() << "\" `!(zi:real#real). BND ("
        << display(dst) << ":real) zi ==> BND (" << display(src) << ":real) zi`;;\n";
  return name.str();
}

static struct holl_backend dummy;
