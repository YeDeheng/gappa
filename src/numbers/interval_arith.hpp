/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#ifndef NUMBERS_INTERVAL_ARITH_HPP
#define NUMBERS_INTERVAL_ARITH_HPP

#include "interval.hpp"

interval operator+(interval const &, interval const &);
interval operator-(interval const &, interval const &);
interval operator*(interval const &, interval const &);
interval operator/(interval const &, interval const &);
interval operator-(interval const &);
interval abs(interval const &);
interval square(interval const &);
interval sqrt(interval const &);
interval log(interval const &);
interval exp(interval const &);
interval log2(interval const &);
interval exp2(interval const &);
interval compose_relative(interval const &, interval const &);
interval compose_relative_inv(interval const &, interval const &);
interval add_relative(interval const &, interval const &, interval const &);

#endif // NUMBERS_INTERVAL_ARITH_HPP
