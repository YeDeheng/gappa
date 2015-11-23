/*
   Copyright (C) 2004 - 2012 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <cassert>
#include <cstring>
#include <iostream>
#include <sstream>
#include "backends/backend.hpp"
#include "backends/coq_common.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"
#include "utils.hpp"

#define GAPPADEF "Gappa.Gappa_definitions."
#define COQRDEF "Reals.Rdefinitions."
#define FLOCQDEF "Flocq.Core.Fcore_"

extern std::string get_real_split(number const &f, int &exp, bool &zero, bool);

namespace coq {

static char const *theorem_defs[][2] = {
  { "subset", "$gpred_bnd.$t $x $1i $i $" },
  { "subset_l", "$gpred_bnd.$t $x $1i $l $" },
  { "subset_r", "$gpred_bnd.$t $x $1i $u $" },
  { "abs_subset", "$gpred_abs.$t $x $1i $i $" },
  { "rel_subset", "$gpred_rel.$t $x $y $1i $i $" },
  { "fix_subset", "$gpred_fixflt.$t $x $1c $c $" },
  { "flt_subset", "$gpred_fixflt.$t $x $1c $c $" },

  { "intersect", "$gpred_bnd.$t $x $1i $2i $i $" },
  { "intersect_hb", "$gpred_bnd.$t $x $1u $2i $i $" },
  { "intersect_bh", "$gpred_bnd.$t $x $2l $1i $i $" },
  { "intersect_hh", "$gpred_bnd.$t $x $1u $2l $i $" },
  { "intersect_aa", "$gpred_abs.$t $x $1i $2i $i $" },
  { "intersect_rr", "$gpred_rel.$t $x $y $1i $2i $i $" },
  { "intersect_rr0", "$gpred_rel.$t $1x $1y $1i $2i $i $" },
  { "absurd_intersect", "$gpred_bnd.$t $1x $1i $2i $" },
  { "absurd_intersect_hb", "$gpred_bnd.$t $1x $1u $2i $" },
  { "absurd_intersect_bh", "$gpred_bnd.$t $1x $1i $2l $" },
  { "absurd_intersect_aa", "$gpred_abs.$t $1x $1i $2i $" },

  { "bnd_of_abs", "$gpred_abs.$t $1x $1i $i $" },
  { "abs_of_bnd_p", "$gpred_abs.$t $1x $1i $i $" },
  { "abs_of_bnd_o", "$gpred_abs.$t $1x $1i $i $" },
  { "abs_of_bnd_n", "$gpred_abs.$t $1x $1i $i $" },
  { "abs_of_uabs", "$gpred_abs.$t $x $1i $" },
  { "uabs_of_abs", "$gpred_abs.$t $1x $i $1p" },
  { "bnd_of_bnd_abs_p", "$gpred_abs.$t $1x $1i $2i $i $" },
  { "bnd_of_bnd_abs_n", "$gpred_abs.$t $1x $1i $2i $i $" },

  { "constant1", "$gpred_bnd.$t _ $i $" },
  { "constant2", "$gpred_bnd.$t _ $i $" },
  { "constant10", "$gpred_bnd.$t _ $i $" },

  { "neg", "$gpred_bnd.$t $1x $1i $i $" },
  { "add", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "sub", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "mul_pp", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "mul_po", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "mul_pn", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "mul_op", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "mul_oo", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "mul_on", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "mul_np", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "mul_no", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "mul_nn", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "div_pp", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "div_pn", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "div_op", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "div_on", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "div_np", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "div_nn", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "square", "$gpred_bnd.$t $1x $1i $i $" },
  { "sqrt", "$gpred_bnd.sqrtG $1x $1i $i $" },

  { "sub_refl", "$gpred_bnd.$t _ $i $" },
  { "div_refl", "$gpred_bnd.$t $1x $i $" },
  { "sub_of_eql", "$gpred_bnd.$t $1x $1y $i $" },
  { "eql_of_cst", "$gpred_bnd.$t $1x $2x $1i $2i $" },

  { "neg_a", "$gpred_abs.$t $1x $i $1p" },
  { "add_aa_p", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "add_aa_o", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "add_aa_n", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "sub_aa_p", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "sub_aa_o", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "sub_aa_n", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "mul_aa", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "div_aa", "$gpred_abs.$t $1x $2x $1i $2i $i $" },

  { "add_rr", "$gpred_rel.$t $1x $1y $2x $2y $1i $2i $3i $i $1p $2p $3p $4p $b" },
  { "sub_rr", "$gpred_rel.$t $1x $1y $2x $2y $1i $2i $3i $i $1p $2p $3p $4p $b" },
  { "mul_rr", "$gpred_rel.$t $1x $1y $2x $2y $1i $2i $i $" },
  { "div_rr", "$gpred_rel.$t $1x $1y $2x $3x $1i $2i $i $" },
  { "inv_r", "$gpred_rel.$t $1x $1y _ $1i $i $1p $2p $b" },
  { "compose", "$gpred_rel.$t $1x $1y $2y $1i $2i $i $" },
  { "compose_swap", "$gpred_rel.$t $1x $y $2x $3x $1i $2i $i $" },
  { "bnd_div_of_rel_bnd_div", "$gpred_rel.$t $1x $1y $3x $1i $2i $i $" },

  { "add_fix", "$gpred_fixflt.$t $1x $2x $1c $2c $c $" },
  { "sub_fix", "$gpred_fixflt.$t $1x $2x $1c $2c $c $" },
  { "mul_fix", "$gpred_fixflt.$t $1x $2x $1c $2c $c $" },
  { "mul_flt", "$gpred_fixflt.$t $1x $2x $1c $2c $c $" },
  { "sub_flt", "$gpred_fixflt.$t $1x $2x $1c $2c $3i $c $" },
  { "sub_flt_rev", "$gpred_fixflt.$t $1x $2x $1c $2c $3i $c $" },

  { "neg_nzr", "$gpred_nzr.$t $1x $1p" },
  { "mul_nzr", "$gpred_nzr.$t $1x $2x $1p $2p" },
  { "div_nzr", "$gpred_nzr.$t $1x $2x $1p $2p" },
  { "nzr_of_abs", "$gpred_nzr.$t $x $1i $" },
  { "nzr_of_nzr_rel", "$gpred_nzr.$t $x $1x $2i $" },
  { "nzr_of_nzr_rel_rev", "$gpred_nzr.$t $1x $x $2i $1p $2p" },

  { "rel_refl", "$gpred_rel.$t $x $i $" },
  { "bnd_of_nzr_rel", "$gpred_rel.$t $2x $1x $i $1p $2p" },
  { "rel_of_nzr_bnd", "$gpred_rel.$t $x $1x $2i $1p $2p" },
  { "error_of_rel_pp", "$gpred_rel.$t $1x $2x $1i $2i $i $" },
  { "error_of_rel_po", "$gpred_rel.$t $1x $2x $1i $2i $i $" },
  { "error_of_rel_pn", "$gpred_rel.$t $1x $2x $1i $2i $i $" },
  { "error_of_rel_op", "$gpred_rel.$t $1x $2x $1i $2i $i $" },
  { "error_of_rel_oo", "$gpred_rel.$t $1x $2x $1i $2i $i $" },
  { "error_of_rel_on", "$gpred_rel.$t $1x $2x $1i $2i $i $" },
  { "error_of_rel_np", "$gpred_rel.$t $1x $2x $1i $2i $i $" },
  { "error_of_rel_no", "$gpred_rel.$t $1x $2x $1i $2i $i $" },
  { "error_of_rel_nn", "$gpred_rel.$t $1x $2x $1i $2i $i $" },
  { "bnd_of_bnd_rel_p", "$gpred_rel.$t $2x $2y $1i $2i $i $" },
  { "bnd_of_bnd_rel_o", "$gpred_rel.$t $2x $2y $1i $2i $i $" },
  { "bnd_of_bnd_rel_n", "$gpred_rel.$t $2x $2y $1i $2i $i $" },
  { "bnd_of_rel_bnd_p", "$gpred_rel.$t $2x $2y $1i $2i $i $" },
  { "bnd_of_rel_bnd_o", "$gpred_rel.$t $2x $2y $1i $2i $i $" },
  { "bnd_of_rel_bnd_n", "$gpred_rel.$t $2x $2y $1i $2i $i $" },

  { "fix_of_singleton_bnd", "$gpred_fixflt.$t $x $1i $c $" },
  { "flt_of_singleton_bnd", "$gpred_fixflt.$t $x $1i $c $" },
  { "fix_of_flt_bnd", "$gpred_fixflt.$t $1x $2i $c $1c $" },
  { "flt_of_fix_bnd", "$gpred_fixflt.$t $1x $2i $1c $c $" },

  { "fix_of_float", "$gfloat.$t _ _ _ _ $c $" },
  { "flt_of_float", "$gfloat.$t _ _ _ $c _ $" },
  { "float_of_fix_flt", "$gfloat.$t _ $1x $1c _ $2c _ $" },
  { "fix_float_of_fix", "$gfloat.$t _ _ _ $1c $c $1x $" },
  { "flt_float_of_flt", "$gfloat.$t _ _ _ $1c $c $1x $" },

  { "float_round_dn", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_round_up", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_round_zr", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_round_ne", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_round_na", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_enforce", "$gfloat.$t _ _ _ _ $1i $i $" },
  { "float_absolute_ne", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_absolute_na", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_absolute_wide_ne", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_absolute_inv_ne", "$gfloat.$t _ _ _ $1i $i $" },
  { "float_absolute_inv_na", "$gfloat.$t _ _ _ $1i $i $" },
  { "float_relative_ne", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_relative_na", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_relative_inv_ne", "$gfloat.$t _ _ $y $1i $i $" },
  { "float_relative_inv_na", "$gfloat.$t _ _ $y $1i $i $" },
  { "rel_of_fix_float_ne", "$gfloat.$t _ _ $1c $1x $i $" },
  { "rel_of_fix_float_na", "$gfloat.$t _ _ $1c $1x $i $" },

  { "fix_of_fixed", "$gfixed.$t _ _ _ $c $" },
  { "fixed_of_fix", "$gfixed.$t _ $1x $1c _ $" },
  { "fix_fixed_of_fix", "$gfixed.$t _ _ $1c $c $1x $" },
  { "flt_fixed_of_flt", "$gfixed.$t _ _ $1c $c $1x $" },
  { "bnd_of_bnd_fix", "$gfixed.$t $1x $2c $1i $i $" },

  { "fixed_round_dn", "$gfixed.$t _ $1x $1i $i $" },
  { "fixed_round_up", "$gfixed.$t _ $1x $1i $i $" },
  { "fixed_round_zr", "$gfixed.$t _ $1x $1i $i $" },
  { "fixed_round_ne", "$gfixed.$t _ $1x $1i $i $" },
  { "fixed_error_dn", "$gfixed.$t _ _ $i $" },
  { "fixed_error_ne", "$gfixed.$t _ _ $i $" },

  { "bnd_rewrite", "$grewriting.$t $1x $1y $i $1p $2p" },
  { "abs_rewrite", "$grewriting.$t $1x $1y $i $1p $2p" },
  { "fix_rewrite", "$grewriting.$t $1x $1y $c $1p $2p" },
  { "flt_rewrite", "$grewriting.$t $1x $1y $c $1p $2p" },
  { "nzr_rewrite", "$grewriting.$t $1x $1y $1p $2p" },
  { "rel_rewrite_1", "$grewriting.$t $1x $1y $y $i $1p $2p" },
  { "rel_rewrite_2", "$grewriting.$t $1x $1y $x $i $1p $2p" },
  { "eql_trans", "$grewriting.$t $x $1y $y $1p $2p" },

  { "opp_mibs", "$grewriting.$t _ _ $i $1p" },
  { "add_xals", "$grewriting.$t _ _ _ $i $1p" },
  { "add_xars", "$grewriting.$t _ _ _ $i $1p" },
  { "sub_xals", "$grewriting.$t _ _ _ $i $1p" },
  { "sub_xars", "$grewriting.$t _ _ _ $i $1p" },
  { "mul_xals", "$grewriting.$t _ _ _ $i $1p" },
  { "mul_xars", "$grewriting.$t _ _ _ $i $1p" },
  { "add_mibs", "$grewriting.$t _ _ _ _ $i $1p" },
  { "add_fils", "$grewriting.$t _ _ _ $i $1p" },
  { "add_firs", "$grewriting.$t _ _ _ $i $1p" },
  { "add_filq", "$grewriting.$t _ _ _ $i $1p $2p" },
  { "add_firq", "$grewriting.$t _ _ _ $i $1p $2p" },
  { "sub_mibs", "$grewriting.$t _ _ _ _ $i $1p" },
  { "sub_fils", "$grewriting.$t _ _ _ $i $1p" },
  { "sub_firs", "$grewriting.$t _ _ _ $i $1p" },
  { "sub_filq", "$grewriting.$t _ _ _ $i $1p $2p" },
  { "sub_firq", "$grewriting.$t _ _ _ $i $1p $2p" },
  { "mul_fils", "$grewriting.$t _ _ _ $i $1p" },
  { "mul_firs", "$grewriting.$t _ _ _ $i $1p" },
  { "mul_mals", "$grewriting.$t _ _ _ _ $i $1p" },
  { "mul_mars", "$grewriting.$t _ _ _ _ $i $1p" },
  { "mul_mabs", "$grewriting.$t _ _ _ _ $i $1p" },
  { "mul_mibs", "$grewriting.$t _ _ _ _ $i $1p" },
  { "err_xalq", "$grewriting.$t _ $2x $3x $i $1p $2p $3p" },
  { "sqrt_mibs", "$grewriting.$t $1x $2x $1i $2i $3i $" },
  { "sqrt_mibq", "$grewriting.$t $1x $2x $1i $2i $3i $" },
  { "val_xebs", "$grewriting.$t $x _ $i $1p" },
  { "val_xabs", "$grewriting.$t _ $x $i $1p" },
  { "div_mibq", "$grewriting.$t _ $1x $2x $3x $i $1p $2p $3p $4p" },
  { "div_xals", "$grewriting.$t _ _ $1x $i $1p $2p" },
  { "div_fil", "$grewriting.$t $1x $2x $i $1p $2p" },
  { "div_fir", "$grewriting.$t $2x $1x $i $1p $2p" },
  { "err_xabq", "$grewriting.$t _ $1x $i $1p $2p" },
  { "err_fabq", "$grewriting.$t _ $1x $i $1p $2p" },
  { "addf_1", "$grewriting.$t $1x _ $i $1p $2p $3p" },
  { "addf_2", "$grewriting.$t _ _ $i $1p $2p" },
  { "addf_3", "$grewriting.$t $1x _ $i $1p $2p $3p" },
  { "addf_4", "$grewriting.$t _ _ $i $1p $2p" },
  { "addf_5", "$grewriting.$t _ $1x $i $1p $2p $3p" },
  { "addf_6", "$grewriting.$t _ _ $i $1p $2p" },
  { "addf_7", "$grewriting.$t _ $1x $i $1p $2p $3p" },
  { "addf_8", "$grewriting.$t _ _ $i $1p $2p" },

  { "opp_fibq", "$grewriting.$t $1x $1y $i $1p" },
  { "mul_filq", "$grewriting.$t _ $1x $1y $i $1p" },
  { "mul_firq", "$grewriting.$t $1x _ $1y $i $1p" },
  { "div_firq", "$grewriting.$t $1x _ $1y $i $1p" },

  { "opp_fibe", "$grewriting.$t $1x $1y $1p" },
  { "add_file", "$grewriting.$t _ $1x $1y $1p" },
  { "add_fire", "$grewriting.$t $1x _ $1y $1p" },
  { "sub_file", "$grewriting.$t _ $1x $1y $1p" },
  { "sub_fire", "$grewriting.$t $1x _ $1y $1p" },
  { "mul_file", "$grewriting.$t _ $1x $1y $1p" },
  { "mul_fire", "$grewriting.$t $1x _ $1y $1p" },
  { "div_file", "$grewriting.$t _ $1x $1y $1p" },
  { "div_fire", "$grewriting.$t $1x _ $1y $1p" },

  { NULL, NULL }
};

theorem_map theorems;

RUN_ONCE(fill_theorem_map)
{
  for (char const *(*p)[2] = theorem_defs; (*p)[0]; ++p) {
    theorems.insert(std::pair<std::string, char const *>((*p)[0], (*p)[1]));
  }
};

bool fqn = false;
bool vernac = true;

static std::string qualify(std::string const &path)
{
  if (fqn) return path;
  else return std::string();
}

std::string convert_name(std::string const &name)
{
  std::string::size_type p0 = name.find(',');
  if (p0 == std::string::npos) return name;
  std::string prefix = name.substr(0, p0);
  std::string::size_type p1 = name.find(',', p0 + 1);
  std::ostringstream res;
  if (prefix == "rounding_fixed")
  {
    assert(p1 != std::string::npos);
    res << '(' << qualify(FLOCQDEF "generic_fmt.") << "round "
        << qualify(GAPPADEF) << "radix2 ("
        << qualify(FLOCQDEF "FIX.") << "FIX_exp ("
        << name.substr(p1 + 1) << ")) ";
    round_mode:
    assert(p1 == p0 + 3);
    std::string mode = name.substr(p0 + 1, 2);
    if (mode == "ne") res << qualify(FLOCQDEF "rnd_ne.") << "rndNE";
    else res << qualify(FLOCQDEF "generic_fmt.") << "rnd"
             << (char)std::toupper(mode[0]) << (char)std::toupper(mode[1]);
    res << ") ";
    return res.str();
  }
  if (prefix == "rounding_float")
  {
    std::string::size_type p2 = name.find(',', p1 + 1);
    assert(p2 != std::string::npos);
    res << '(' << qualify(FLOCQDEF "generic_fmt.") << "round "
        << qualify(GAPPADEF) << "radix2 ("
        << qualify(FLOCQDEF "FLT.") << "FLT_exp ("
        << name.substr(p2 + 1) << ") (" << name.substr(p1 + 1, p2 - p1 - 1) << ")) ";
    goto round_mode;
  }
  bool fragile = false;
  res << prefix;
  do {
    std::string::size_type p1 = p0 + 1;
    p0 = name.find(',', p1);
    std::string s(name, p1, p0 == std::string::npos ? p0 : p0 - p1);
    if (!std::isalpha(s[0])) {
      res << " (" << s << ')';
      fragile = true;
    } else res << '_' << s;
  } while (p0 != std::string::npos);
  if (!fragile) return res.str();
  return '(' + res.str() + ')';
}

static id_cache< std::string > displayed_floats;

std::string display(number const &f)
{
  std::ostringstream s;
  bool zero;
  int exp;
  s << '(' << get_real_split(f, exp, zero, false);
  s << ") (" << (zero ? 0 : exp) << ')';
  std::string const &s_ = s.str();
  int f_id = displayed_floats.find(s_);
  std::string name = composite('f', f_id);
  if (f_id < 0) return name;
  *out << (vernac ? "Definition " : "let ") << name << " := "
       << qualify(GAPPADEF) << "Float2 " << s_
       << (vernac ? ".\n" : " in\n");
  return name;
}

static id_cache< std::string > displayed_intervals;

std::string display(interval const &i)
{
  std::ostringstream s;
  s << display(lower(i)) << ' ' << display(upper(i));
  std::string const &s_ = s.str();
  int i_id = displayed_intervals.find(s_);
  std::string name = composite('i', i_id);
  if (i_id < 0) return name;
  *out << (vernac ? "Definition " : "let ") << name << " := "
       << qualify(GAPPADEF) << "makepairF " << s_
       << (vernac ? ".\n" : " in\n");
  return name;
}

static id_cache< ast_real const * > displayed_reals;

std::ostream *out_vars;

std::string display(ast_real const *r)
{
  if (hidden_real const *h = boost::get< hidden_real const >(r))
    r = h->real;
  int r_id = displayed_reals.find(r);
  std::string name = r->name ? '_' + r->name->name : composite('r', r_id);
  if (r_id < 0)
    return name;
  if (boost::get< undefined_real const >(r)) {
    *out_vars << (vernac ? "Variable " : " (") << name << " : "
              << qualify(COQRDEF) << 'R' << (vernac ? ".\n" : ")");
    return name;
  }
  auto_flush plouf;
  plouf << (vernac ? "Notation " : "let ") << name << " := ";
  if (vernac) plouf << '(';
  if (ast_number const *const *nn = boost::get< ast_number const *const >(r))
  {
    ast_number const &n = **nn;
    std::string m = (n.mantissa.size() > 0 && n.mantissa[0] == '+') ? n.mantissa.substr(1) : n.mantissa;
    if (n.base == 0)
      plouf << qualify("Gappa.Gappa_pred_bnd.") << "Float1 0";
    else if (n.exponent == 0)
      plouf << qualify("Gappa.Gappa_pred_bnd.") << "Float1 (" << m << ')';
    else
      plouf << qualify(GAPPADEF) << "float" << n.base << "R ("
            << qualify(GAPPADEF) << "Float" << n.base
            << " (" << m << ") (" << n.exponent << "))";
  }
  else if (real_op const *o = boost::get< real_op const >(r))
  {
    static char const op[] = "X-XX+-*/XX";
    if (o->type == ROP_FUN)
    {
      std::string description = o->fun->description();
      plouf << convert_name(description) << ' ' << display(o->ops[0]);
      for (ast_real_vect::const_iterator i = ++(o->ops.begin()),
           end = o->ops.end(); i != end; ++i)
        plouf << ' ' << display(*i);
    }
    else if (fqn)
    {
      char const *s;
      switch (o->type) {
      case BOP_ADD: s = COQRDEF "Rplus"; break;
      case BOP_SUB: s = COQRDEF "Rminus"; break;
      case BOP_MUL: s = COQRDEF "Rmult"; break;
      case BOP_DIV: s = COQRDEF "Rdiv"; break;
      case UOP_ABS: s = "Reals.Rbasic_fun.Rabs"; break;
      case UOP_SQRT: s = "Reals.R_sqrt.sqrt"; break;
      case UOP_NEG: s = COQRDEF "Ropp"; break;
      default: assert(false);
      }
      plouf << s << ' ' << display(o->ops[0]);
      if (o->ops.size() == 2) plouf << ' ' << display(o->ops[1]);
    }
    else if (o->ops.size() == 1)
    {
      std::string s(1, op[o->type]);
      if (o->type == UOP_ABS) s = "Rabs";
      else if (o->type == UOP_SQRT) s = "sqrt";
      plouf << '(' << s << ' ' << display(o->ops[0]) << ")%R";
    }
    else
    {
      plouf << '(' << display(o->ops[0]) << ' ' << op[o->type] << ' '
            << display(o->ops[1]) << ")%R";
    }
  }
  else
    assert(false);
  plouf << (vernac ? ").\n" : " in\n");
  return name;
}

static id_cache<property> displayed_properties;

std::string display(property const &p)
{
  if (p.null()) return "False";
  int p_id = displayed_properties.find(p);
  std::string name = composite('p', p_id);
  if (p_id < 0) return name;
  std::ostringstream s;
  predicate_type t = p.real.pred();
  ast_real const *real = p.real.real();
  if (p.real.pred_bnd())
  {
    interval const &bnd = p.bnd();
    if (lower(bnd) == number::neg_inf) {
      assert(t == PRED_BND);
      if (fqn)
        s << COQRDEF "Rle " << display(real) << ' ' << display(upper(bnd));
      else
        s << '(' << display(real) << " <= " << display(upper(bnd)) << ")%R";
    } else if (upper(bnd) == number::pos_inf) {
      assert(t == PRED_BND);
      if (fqn)
        s << COQRDEF "Rle " << display(lower(bnd)) << ' ' << display(real);
      else
        s << '(' << display(lower(bnd)) << " <= " << display(real) << ")%R";
    }
    else
    {
      switch (t) {
      case PRED_BND:
        s << qualify(GAPPADEF) << "BND " << display(real) << ' ' << display(bnd);
        break;
      case PRED_ABS:
        s << qualify(GAPPADEF) << "ABS " << display(real) << ' ' << display(bnd);
        break;
      case PRED_REL:
        s << qualify(GAPPADEF) << "REL " << display(real) << ' '
          << display(p.real.real2()) << ' ' << display(bnd);
        break;
      default:
        assert(false);
      }
    }
  }
  else
  {
    switch (t) {
    case PRED_FIX:
      s << qualify(GAPPADEF) << "FIX " << display(real) << " (" << p.cst() << ')';
      break;
    case PRED_FLT:
      s << qualify(GAPPADEF) << "FLT " << display(real) << " (" << p.cst() << ')';
      break;
    case PRED_EQL:
      s << display(real) << " = " << display(p.real.real2());
      break;
    case PRED_NZR:
      s << qualify(GAPPADEF) << "NZR " << display(real);
      break;
    default:
      assert(false);
    }
  }
  *out << (vernac ? "Notation " : "let ") << name << (vernac ? " := (" : " := ")
       << s.str() << (vernac ? "). (* " : " in (* ") << dump_property(p) << " *)\n";
  return name;
}

static property const &fetch(property const &p)
{
  if (p.real.pred_bnd() && !is_defined(p.bnd())) {
    undefined_map::const_iterator i = instances->find(p.real);
    assert(i != instances->end());
    return i->second;
  }
  return p;
}

static id_cache<property_tree> displayed_trees;

std::string display(property_tree const &t)
{
  if (t.empty()) return "False";
  if (t.atom && t.conjunction) return display(fetch(*t.atom));
  int t_id = displayed_trees.find(t);
  std::string name = composite('s', t_id);
  if (t_id < 0) return name;
  auto_flush plouf;
  plouf << (vernac ? "Definition " : "let ") << name << (vernac ? " := (" : " := ");
  if (!t.left) {
    assert(!t.conjunction);
    plouf << "not " << display(fetch(*t.atom));
  } else {
    plouf << display(*t.left) << (t.conjunction ? " /\\ " : " \\/ ")
      << display(*t.right);
  }
  plouf << (vernac ? ").\n" : " in\n");
  return name;
}

void apply_theorem(auto_flush &plouf, std::string const &th,
  property const &res, property const *hyp, property_map const *pmap, int *num)
{
  theorem_map::const_iterator it = theorems.find(th);
  if (it == theorems.end())
  {
    plouf << "UNKNOWN_" << th;
    return;
  }
  char const *p = it->second.c_str();
  bool has_comp = false;
  int max = 0;
  std::string buf;
  for (; *p; ++p)
  {
    if (*p != '$') { plouf << *p; continue; }
    ++p;
    property const *h = &res;
    if (*p >= '1' && *p <= '9')
    {
      int n = *(p++) - '1';
      h = &hyp[n];
      for (; max <= n; ++max) {
        char t[] = { ' ', '$', '1' + max, 'p', '\0' };
        buf += t;
      }
    }
    switch (*p) {
      case 'g': {
        char const *q = strchr(p + 1, '.');
        assert(q);
        plouf << qualify("Gappa.Gappa_" + std::string(p + 1, q + 1));
        p = q;
        break; }
      case 't': plouf << th; break;
      case 'i': plouf << display(h->bnd()); break;
      case 'l': plouf << display(lower(h->bnd())); break;
      case 'u': plouf << display(upper(h->bnd())); break;
      case 'c': plouf << '(' << h->cst() << ')'; break;
      case 'x': plouf << display(h->real.real()); break;
      case 'y': plouf << display(h->real.real2()); break;
      case '\0':
        has_comp = true;
        p = buf.c_str();
        break;
      case 'p':
        plouf << 'h';
        if (pmap) {
          property_map::const_iterator pki = pmap->find(h->real);
          assert(pki != pmap->end());
          plouf << pki->second.first;
        } else if (num)
          plouf << num[h - hyp];
        else
          plouf << h - hyp;
        break;
      case 'b':
        has_comp = true;
        break;
      default:
        plouf << '$';
    }
  }
  if (has_comp) plouf << " _";
}

std::string display(theorem_node *t)
{
  static int t_id = 0;
  std::string name = composite('t', ++t_id);
  auto_flush plouf;
  if (vernac)
  {
    plouf << "Lemma " << name << " : ";
    for (property_vect::const_iterator i = t->hyp.begin(),
         end = t->hyp.end(); i != end; ++i)
      plouf << display(*i) << " -> ";
    plouf << display(t->res) << ".\n";
    int nb_hyps = t->hyp.size();
    if (nb_hyps)
    {
      plouf << " intros";
      for (int i = 0; i < nb_hyps; ++i) plouf << " h" << i;
      plouf << ".\n";
    }
    plouf << " refine (";
  }
  else
  {
    plouf << "let " << name;
    int num_hyp = 0;
    for (property_vect::const_iterator i = t->hyp.begin(),
         i_end = t->hyp.end(); i != i_end; ++i)
      plouf << " (h" << num_hyp++ << " : " << display(*i) << ')';
    plouf << " : " <<  display(t->res) << " := ";
  }

  apply_theorem(plouf, convert_name(t->name), t->res, &*t->hyp.begin());
  plouf << (vernac ? ") ; finalize.\nQed.\n" : " in\n");
  return name;
}

std::string subset_name(property const &p1, property const &p2)
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

void invoke_lemma(auto_flush &plouf, property_vect const &hyp, property_map const &pmap)
{
  for (property_vect::const_iterator j = hyp.begin(),
       j_end = hyp.end(); j != j_end; ++j)
  {
    property_map::const_iterator pki = pmap.find(j->real);
    assert(pki != pmap.end());
    int h = pki->second.first;
    std::string sn = subset_name(*pki->second.second, *j);
    if (sn.empty()) {
      if (vernac) plouf << " exact h" << h << '.';
      else plouf << " h" << h;
    } else {
      plouf << (vernac ? " refine (" : " (");
      apply_theorem(plouf, sn, *j, pki->second.second, &pmap);
      plouf << (vernac ? ") ; finalize." : ")");
    }
  }
  if (vernac) plouf << '\n';
}

/**
 * Instantiate node @a m as "h @a num_hyp" with the hypotheses of node @a n.
 */
static void pose_hypothesis(auto_flush &plouf, int num_hyp, node *m, node *n)
{
  plouf << (vernac ? " assert (h" : "  let h") << num_hyp << " := ";
  int i = 0;
  graph_t *g = n->graph;
  for (; g != m->graph; g = g->get_father()) ++i;
  if (m->type == LOGIC && !static_cast<logic_node *>(m)->before) {
    plouf << 'h' << i;
  } else {
    plouf << display(m);
    for (; g; g = g->get_father()) plouf << " h" << (i++);
  }
  plouf << (vernac ? ").\n" : " in\n");
}

typedef std::map<ast_real const *, int> real_map;

static int find_real(real_map &rm, ast_real const *r)
{
  real_map::const_iterator i = rm.find(r);
  if (i == rm.end()) {
    int j = rm.size();
    rm[r] = j;
    return j;
  }
  return i->second;
}

static void reify(auto_flush &plouf, real_map &rm, property const &p)
{
  switch (p.real.pred()) {
  case PRED_BND: {
    interval const &b = p.bnd();
    int r = find_real(rm, p.real.real());
    if (is_bounded(b))
      plouf << "Abnd " << r << "%nat " << display(b);
    else if (lower(b) == number::neg_inf)
      plouf << "Aleq " << r << "%nat " << display(upper(b));
    else
      plouf << "Ageq " << r << "%nat " << display(lower(b));
    break; }
  case PRED_ABS:
    plouf << "Aabs " << find_real(rm, p.real.real()) << "%nat " << display(p.bnd());
    break;
  case PRED_REL:
    plouf << "Arel " << find_real(rm, p.real.real()) << "%nat " << find_real(rm, p.real.real2()) << "%nat " << display(p.bnd());
    break;
  case PRED_FIX:
    plouf << "Afix " << find_real(rm, p.real.real()) << "%nat (" << p.cst() << ")%Z";
    break;
  case PRED_FLT:
    plouf << "Aflt " << find_real(rm, p.real.real()) << "%nat " << p.cst() << "%positive";
    break;
  case PRED_NZR:
    plouf << "Anzr " << find_real(rm, p.real.real()) << "%nat";
    break;
  case PRED_EQL:
    plouf << "Aeql " << find_real(rm, p.real.real()) << "%nat " << find_real(rm, p.real.real2()) << "%nat";
    break;
  }
}

static void reify(auto_flush &plouf, real_map &rm, property_tree const &t)
{
  assert(!t.empty());
  if (t.left) {
    plouf << "(Ttree " << (t.conjunction ? "true" : "false") << ' ';
    reify(plouf, rm, *t.left);
    plouf << ' ';
    reify(plouf, rm, *t.right);
    plouf << ')';
  } else {
    plouf << "(Tatom " << (t.conjunction ? "true" : "false") << " (";
    reify(plouf, rm, fetch(*t.atom));
    plouf << "))";
  }
}

static void simplification(auto_flush &plouf, property_tree const &before, property_tree const &after, property const &mod, int num_hyp)
{
  real_map rm;
  if (vernac) plouf << " refine ";
  plouf << "(simplify ";
  reify(plouf, rm, before);
  plouf << ' ';
  if (after.empty()) plouf << "Tfalse";
  else reify(plouf, rm, after);
  plouf << " (";
  reify(plouf, rm, mod);
  plouf << ") ";
  std::vector<ast_real const *> inv(rm.size(), NULL);
  for (real_map::const_iterator i = rm.begin(), i_end = rm.end(); i != i_end; ++i)
  {
    inv[i->second] = i->first;
  }
  for (std::vector<ast_real const *>::const_iterator i = inv.begin(),
       i_end = inv.end(); i != i_end; ++i)
  {
    plouf << "(List.cons " << display(*i) << ' ';
  }
  plouf << "List.nil" << std::string(rm.size(), ')')
     << " h" << num_hyp << " h" << (num_hyp - 1) << " _)";
  if (vernac) plouf << " ; finalize.\n";
}

static void select(auto_flush &plouf, int idx, int num_hyp)
{
  if (vernac) plouf << " exact (";
  if (idx) plouf << "proj" << idx << ' ';
  plouf << 'h' << num_hyp;
  if (vernac) plouf << ").\n";
}

static id_cache< node * > displayed_nodes;

std::string display(node *n)
{
  assert(n);
  int n_id = displayed_nodes.find(n);
  std::string name = composite('l', n_id);
  if (n_id < 0) return name;
  auto_flush plouf;
  if (vernac) plouf << "Lemma " << name << " : ";
  else plouf << "let " << name << " : ";
  int num_hyp = 0;
  for (graph_t *g = n->graph; g; g = g->get_father())
  {
    plouf << display(g->get_hypotheses()) << " -> ";
    ++num_hyp;
  }
  logic_node *ln = NULL;
  if (n->type == LOGIC) {
    ln = static_cast<logic_node *>(n);
    assert(ln->before);
    plouf << display(ln->tree);
  } else {
    property const &n_res = n->get_result();
    if (n_res.null())
      plouf << "False";
    else
      plouf << display(n_res) << " (* " << dump_property(n_res) << " *)";
  }
  plouf << (vernac ? ".\n" : " :=\n");
  if (num_hyp) {
    plouf << (vernac ? " intros" : " fun");
    for (int i = 0; i < num_hyp; ++i) plouf << " h" << i;
    plouf << (vernac ? ".\n" : " =>\n");
  }
  switch (n->type) {
  case LOGIC: {
    pose_hypothesis(plouf, num_hyp, ln->before, n);
    if (ln->modifier) {
      pose_hypothesis(plouf, ++num_hyp, ln->modifier, n);
      simplification(plouf, ln->before->tree, ln->tree, ln->modifier->get_result(), num_hyp);
    } else {
      assert(ln->before->tree.conjunction);
      select(plouf, ln->index, num_hyp);
    }
    break; }
  case LOGICP: {
    logicp_node *ln = static_cast<logicp_node *>(n);
    assert(ln->before && ln->before->tree.conjunction);
    pose_hypothesis(plouf, num_hyp, ln->before, n);
    select(plouf, ln->index, num_hyp);
    break; }
  case MODUS: {
    property_map pmap;
    node_vect const &pred = n->get_subproofs();
    for (node_vect::const_iterator i = pred.begin(),
         i_end = pred.end(); i != i_end; ++i)
    {
      node *m = *i;
      pose_hypothesis(plouf, num_hyp, m, n);
      property const &res = m->get_result();
      pmap[res.real] = std::make_pair(num_hyp++, &res);
    }
    modus_node *mn = static_cast<modus_node *>(n);
    assert(mn->target);
    plouf << (vernac ? " apply " : "  ") << display(mn->target);
    if (vernac) plouf << '.';
    invoke_lemma(plouf, mn->target->hyp, pmap);
    break; }
  case INTERSECTION: {
    property hyps[2];
    node_vect const &pred = n->get_subproofs();
    int num[2];
    char const *suffix = "", *prefix = "";
    property const &n_res = n->get_result();
    if (n_res.null()) prefix = "absurd_";
    for (int i = 0; i < 2; ++i)
    {
      node *m = pred[i];
      property const &res = m->get_result();
      hyps[i] = res;
      switch (res.real.pred()) {
        case PRED_BND:
          if (!is_bounded(res.bnd()))
            if (!i) suffix = "_hb";
            else if (suffix[0]) suffix = "_hh";
            else suffix = "_bh";
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
      pose_hypothesis(plouf, num_hyp, m, n);
      num[i] = num_hyp++;
    }
    if (vernac) {
      plouf << " apply " << prefix << "intersect" << suffix << " with"
               " (1 := h" << num[0] << ") (2 := h" << num[1] << ")."
               " finalize.\n";
    } else {
      plouf << "  ";
      apply_theorem(plouf, std::string(prefix) + "intersect" + suffix,
                    n_res, hyps, NULL, num);
    }
    break; }
  case UNION: {
    node_vect const &pred = n->get_subproofs();
    property const &n_res = n->get_result();
    assert(pred.size() >= 2);
    node *mcase = pred[0];
    property const &pcase = mcase->get_result();
    assert(pcase.real.pred() == PRED_BND);
    pose_hypothesis(plouf, num_hyp, mcase, n);
    if (vernac) plouf << " revert h" << num_hyp << ".\n";
    for (node_vect::const_iterator i = pred.begin() + 1,
         i_end = pred.end(); i != i_end; ++i)
    {
      node *m = *i;
      property const &p = *m->graph->get_hypotheses().atom;
      plouf << (vernac ? " assert (u : " : "  let u : ")
        << display(p) << " -> " << display(n_res)
        << (vernac ? "). intro h" : " := fun h") << num_hyp
        << (vernac ? ". (* " : " => (* ") << p.bnd() << " *)\n";
      property const &res = m->get_result();
      if (res.null()) {
        if (n_res.null())
          plouf << (vernac ? " apply (" : "   (");
        else
          plouf << (vernac ? " elim (" : " False_ind _ (");
      } else {
        // not a contradictory result
        std::string sn = subset_name(res, n_res);
        if (!sn.empty()) {
          assert(vernac);
          plouf << " apply " << sn << " with ";
          switch (res.real.pred()) {
          case PRED_FIX: plouf << res.cst() << "%Z"; break;
          case PRED_FLT: plouf << res.cst() << "%positive"; break;
          default: plouf << display(res.bnd());
          }
          plouf << ". 2: finalize.\n";
        }
        plouf << (vernac ? " apply (" : " (");
      }
      plouf << display(m) << " h" << num_hyp;
      for (int j = 0; j != num_hyp; ++j) plouf << " h" << j;
      plouf << (vernac ? ").\n" : ") in\n");
      if (i + 1 != i_end)
        if (vernac)
          plouf << " next_interval (union) u.\n";
        else
          plouf << "  Gappa.Gappa_pred_bnd.union " << display(pcase.real.real())
            << ' ' << display(n_res) << " (" GAPPADEF "makepairF _ _) _ u _ (\n";
      else
        plouf << (vernac ? " exact u.\n" : "  u");
    }
    if (!vernac) plouf << std::string(pred.size() - 2, ')') << " h" << num_hyp;
    break; }
  }
  plouf << (vernac ? "Qed.\n" : " in\n");
  return name;
}

}
