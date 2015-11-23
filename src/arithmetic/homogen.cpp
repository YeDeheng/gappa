/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include "parser/ast.hpp"
#include "numbers/interval_arith.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"

struct homogen_rounding_class: function_class
{
  default_function_generator generator;
  interval he;
  homogen_rounding_class();
  virtual interval absolute_error_from_exact_bnd(interval const &, std::string &) const;
  virtual std::string description() const { return "homogen80x"; }
  virtual std::string pretty_name() const { return "homogen80x"; }
};

homogen_rounding_class::homogen_rounding_class()
  : function_class(UOP_ID, TH_ABS_EXA_BND), generator("homogen80x", this) {
  he = from_exponent(-53, 0) + from_exponent(-64, 0);
}

interval homogen_rounding_class::absolute_error_from_exact_bnd(interval const &i, std::string &name) const {
  name = "homogen80x_error";
  return i * he;
}

static homogen_rounding_class dummy;

struct homogen_init_rounding_class: function_class
{
  default_function_generator generator;
  interval he;
  homogen_init_rounding_class();
  virtual interval absolute_error_from_approx_bnd(interval const &, std::string &) const;
  virtual std::string description() const { return "homogen80x_init"; }
  virtual std::string pretty_name() const { return "homogen80x_init"; }
};

homogen_init_rounding_class::homogen_init_rounding_class()
  : function_class(UOP_ID, TH_ABS_APX_BND), generator("homogen80x_init", this) {
  he = from_exponent(-53, 0) + from_exponent(-64, 0);
}

interval homogen_init_rounding_class::absolute_error_from_approx_bnd(interval const &i, std::string &name) const {
  name = "homogen80x_init_error";
  return i * he;
}

static homogen_init_rounding_class dummy_init;

struct floatx_rounding_class: function_class {
  default_function_generator generator;
  floatx_rounding_class();
  virtual interval round(interval const &, std::string &) const;
  virtual std::string description() const { return "float80x"; }
  virtual std::string pretty_name() const { return "float80x"; }
};

floatx_rounding_class::floatx_rounding_class()
  : function_class(UOP_ID, TH_RND), generator("float80x", this) {
}

struct floatx_format: gs_rounding {
  virtual int shift_val(int exp, int sz) const { return std::max(-1074 - exp, sz - 53); }
};

interval floatx_rounding_class::round(interval const &i, std::string &name) const {
  static floatx_format format;
  number a = round_number(lower(i), &format, &floatx_format::roundDN);
  number b = round_number(upper(i), &format, &floatx_format::roundUP);
  name = "float80x_round";
  return interval(a, b);
}

static floatx_rounding_class dummy2;
