/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#ifndef UTILS_HPP
#define UTILS_HPP

#define RUN_ONCE(name) \
  struct class_##name { class_##name(); }; \
  static class_##name dummy_##name; \
  class_##name::class_##name()

template<class T>
class static_ptr
{
  T *ptr;
 public:
  ~static_ptr() { delete ptr; }
  T *operator->() { if (!ptr) ptr = new T; return ptr; }
  T &operator*() { if (!ptr) ptr = new T; return *ptr; }
};

#endif // UTILS_HPP
