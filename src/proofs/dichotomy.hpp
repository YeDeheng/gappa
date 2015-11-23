/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#ifndef PROOFS_DICHOTOMY_HPP
#define PROOFS_DICHOTOMY_HPP

#include "proofs/property.hpp"

struct dichotomy_var {
  ast_real const *real;
  unsigned long splitter;
};

struct split_point;

unsigned long fill_splitter(unsigned long, ast_number const *);
unsigned long fill_splitter(unsigned long, split_point const &);

typedef std::vector< dichotomy_var > dvar_vect;

struct dichotomy_hint {
  dvar_vect src;
  property_tree dst;
};

typedef std::vector< dichotomy_hint > dichotomy_sequence;
extern dichotomy_sequence dichotomies;

#endif // PROOFS_DICHOTOMY_HPP
