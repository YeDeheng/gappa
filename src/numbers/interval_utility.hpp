/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#ifndef NUMBERS_INTERVAL_UTILITY_HPP
#define NUMBERS_INTERVAL_UTILITY_HPP

#include <algorithm>
#include <iosfwd>
#include "interval.hpp"

struct number;

interval hull(interval const &, interval const &);
interval intersect(interval const &, interval const &);
interval from_exponent(int exp, int rnd);
std::pair< interval, interval > split(interval const &);
std::pair< interval, interval > split(interval const &, double);
number const &lower(interval const &);
number const &upper(interval const &);
std::ostream &operator<<(std::ostream &, number const &);
std::ostream &operator<<(std::ostream &, interval const &);
int sign(interval const &);
int sign_strict(interval const &);

enum io_format { IO_APPROX, IO_EXACT, IO_FULL };
struct change_io_format {
  static io_format current;
  io_format old;
  change_io_format(io_format f): old(current) { current = f; }
  ~change_io_format() { current = old; }
};

#endif // NUMBERS_INTERVAL_UTILITY_HPP
