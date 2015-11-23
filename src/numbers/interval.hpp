/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#ifndef NUMBERS_INTERVAL_HPP
#define NUMBERS_INTERVAL_HPP

struct interval_base;
struct number;

struct interval {
 //private:
  mutable interval_base const *base;
  interval(interval_base const *b): base(b) {}
 //public:
  interval(): base(0) {}
  interval(number const &, number const &);
  ~interval();
  interval(interval const &);
  interval &operator=(interval const &);
  interval_base *unique() const;
  bool operator<=(interval const &) const;
  bool operator<(interval const &) const;
};

inline bool is_defined(interval const &u) { return u.base; }
bool is_empty(interval const &);
bool is_singleton(interval const &);
bool contains_zero(interval const &);
bool is_zero(interval const &);
bool is_bounded(interval const &);
interval zero();

#endif // NUMBERS_INTERVAL_HPP
