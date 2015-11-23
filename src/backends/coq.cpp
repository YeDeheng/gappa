/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <cctype>
#include <iostream>
#include <ostream>
#include <sstream>
#include "utils.hpp"
#include "backends/backend.hpp"
#include "backends/coq_common.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "parser/pattern.hpp"
#include "proofs/proof_graph.hpp"

using namespace coq;

struct coq_backend: backend {
  coq_backend(): backend("coq") {}
  void initialize(std::ostream &o) {
    out = &o;
    out_vars = &o;
    o << "Require Import Fcore.\n"
         "Require Import Gappa_library.\n"
         "Section Generated_by_Gappa.\n";
  }
  void finalize() { *out << "End Generated_by_Gappa.\n"; }
  std::string rewrite(ast_real const *, ast_real const *, pattern_cond_vect const &);
  std::string theorem(node *n) { return display(n); }
  bool is_known(std::string const &s) { return theorems.count(s); }
};

std::string coq_backend::rewrite(ast_real const *src, ast_real const *dst,
                                 pattern_cond_vect const &pc)
{
  static int a_id = 0;
  ++a_id;
  int nb_hyps = 0;
  std::ostringstream s_hyps, s_intros, s_bool, s_proof, s_dec, s_th;
  bool first_bool = true;
  auto_flush plouf;
  plouf << "Hypothesis a" << a_id << " : ";
  for (pattern_cond_vect::const_iterator i = pc.begin(),
       i_end = pc.end(); i != i_end; ++i)
  {
    std::string var = display(i->real);
    std::string val;
    if (i->type == COND_NZ || i->value == 0) val = "0";
    else
    {
      std::ostringstream val_;
      val_ << "Float1 (" << i->value << ')';
      val = val_.str();
    }
    plouf << '(' << var;
    switch (i->type)
    {
      case COND_NZ:
      case COND_NE: plouf << " <> " << val << ")%R -> "; break;
      case COND_LT: plouf << " < "  << val << ")%R -> "; break;
      case COND_GT: plouf << " > "  << val << ")%R -> "; break;
      case COND_LE: plouf << " <= " << val << ")%R -> "; break;
      case COND_GE: plouf << " >= " << val << ")%R -> "; break;
    }
    if (i->type == COND_NZ)
    {
      s_hyps << "NZR " << var << " -> ";
      s_th << " $" << nb_hyps + 1 << 'p';
      s_intros << " h" << nb_hyps;
      s_proof << " exact h" << nb_hyps << ".\n";
    }
    else
    {
      s_hyps << "forall i" << nb_hyps << " : FF, BND " << var << " i" << nb_hyps << " -> ";
      s_th << " $" << nb_hyps + 1 << "i $" << nb_hyps + 1 << 'p';
      s_intros << " i" << nb_hyps << " h" << nb_hyps;
      std::string s_dec_ = s_dec.str();
      s_dec.str(std::string());
      if (first_bool)
      {
        first_bool = false;
        s_dec << " rename hb into j" << nb_hyps << ".\n";
      }
      else
      {
        s_bool << " && ";
        s_dec << " generalize (andb_prop _ _ hb). clear hb. intros (hb, j" << nb_hyps << ").\n";
      }
      if (i->value == 0)
      {
        char const *s = NULL;
        switch (i->type)
        {
          case COND_LT: s = "lt0"; break;
          case COND_GT: s = "gt0"; break;
          case COND_LE: s = "le0"; break;
          case COND_GE: s = "ge0"; break;
          default: assert(false);
        }
        s_bool << "rewrite_" << s << "_helper i" << nb_hyps;
        s_proof << " apply rewrite_" << s << " with (1 := h" << nb_hyps
                << ") (2 := j" << nb_hyps << ").\n";
      }
      else
      {
        char const *s = NULL;
        switch (i->type)
        {
          case COND_NE: s = "ne"; break;
          case COND_LT: s = "lt"; break;
          case COND_GT: s = "gt"; break;
          case COND_LE: s = "le"; break;
          case COND_GE: s = "ge"; break;
          default: assert(false);
        }
        s_bool << "rewrite_" << s << "_helper i" << nb_hyps << " (" << i->value << ')';
        s_proof << " apply rewrite_" << s << " with (1 := h" << nb_hyps
                << ") (2 := j" << nb_hyps << ").\n";
      }
      s_dec << s_dec_;
    }
    ++nb_hyps;
  }
  plouf << display(src) << " = " << display(dst) << ".\n";
  std::string name = composite('b', a_id);
  plouf << "Lemma " << name << " : " << s_hyps.str();
  if (!first_bool)
  {
    plouf << s_bool.str() << " = true -> ";
    s_intros << " hb";
    s_th << " $b";
  }
  plouf << display(src) << " = " << display(dst) << ".\n";
  if (!s_intros.str().empty()) plouf << " intros" << s_intros.str() << ".\n";
  plouf << s_dec.str() << " apply a" << a_id << ".\n" << s_proof.str() << "Qed.\n";
  theorems.insert(std::make_pair(name, name + s_th.str()));
  return name;
}

static struct coq_backend dummy;
