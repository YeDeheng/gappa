/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include "utils.hpp"
#include "backends/backend.hpp"

std::ostream *out;
undefined_map const *instances;

typedef std::map< std::string, backend * > backend_map;
static static_ptr<backend_map> backends;

backend::backend(std::string const &name)
{
  (*backends)[name] = this;
}

backend *backend::find(std::string const &name) {
  backend_map::const_iterator i = backends->find(name);
  if (i == backends->end()) return NULL;
  return i->second;
}

std::string composite(char prefix, int num) {
  std::ostringstream s;
  s << prefix << (num < 0 ? -num : num);
  return s.str();
}
