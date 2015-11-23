/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#ifndef PARSER_PATTERN_HPP
#define PARSER_PATTERN_HPP

#include "parser/ast_real.hpp"
#include "proofs/property.hpp"

bool match(ast_real const *src, ast_real const *dst, ast_real_vect &, bool = false);
ast_real const *rewrite(ast_real const *, ast_real_vect const &);
int count_missing(ast_real const *);
ast_real const *unhide(ast_real const *);

bool relative_error(ast_real const *, ast_real const *[2]);
function_class const *absolute_rounding_error(ast_real const *, ast_real const *[2]);
function_class const *relative_rounding_error(predicated_real const &);

struct pattern_cond {
  ast_real const *real;
  condition_type type;
  int value;
};

class pattern {
  ast_real const *real;
 public:
  operator ast_real const *() const { return real; }
  pattern(int n): real(normalize(placeholder(n))) {}
  pattern(ast_real const &r): real(normalize(r)) {}
  pattern operator-() const;
  pattern operator+(pattern const &) const;
  pattern operator-(pattern const &) const;
  pattern operator*(pattern const &) const;
  pattern operator/(pattern const &) const;
  pattern_cond operator<(int) const;
  pattern_cond operator>(int) const;
  pattern_cond operator<=(int) const;
  pattern_cond operator>=(int) const;
  pattern_cond operator!=(int) const;
  pattern_cond operator~() const;
  static pattern abs(pattern const &);
  static pattern sqrt(pattern const &);
  static pattern log(pattern const &);
  static pattern exp(pattern const &);
  static pattern log2(pattern const &);
  static pattern exp2(pattern const &);
  static pattern hide(pattern const &);
};

#endif // PARSER_PATTERN_HPP
