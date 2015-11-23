/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#ifndef BACKENDS_BACKEND_HPP
#define BACKENDS_BACKEND_HPP

#include <map>
#include <ostream>
#include <sstream>
#include <string>
#include <vector>

struct node;
struct ast_real;
struct pattern_cond;
struct predicated_real;
struct property;
typedef std::vector< pattern_cond > pattern_cond_vect;
typedef std::map<predicated_real, property> undefined_map;

struct backend
{
  backend(std::string const &);
  virtual void initialize(std::ostream &) = 0;
  virtual std::string rewrite(ast_real const *, ast_real const *, pattern_cond_vect const &) = 0;
  virtual std::string theorem(node *) = 0;
  virtual void finalize() = 0;
  virtual ~backend() {}
  virtual bool is_known(std::string const &) { return true; }
  static backend *find(std::string const &);
};

extern std::ostream *out;
extern undefined_map const *instances;

struct auto_flush: std::ostringstream {
  ~auto_flush() { *::out << str(); }
};

template< class T >
struct id_cache {
  typedef std::map< T, int > store_t;
  store_t store;
  int nb;
 public:
  id_cache(): nb(0) {}
  int find(T const &k) {
    typename store_t::const_iterator it = store.find(k);
    if (it != store.end()) return -it->second;
    int id = ++nb;
    store.insert(std::make_pair(k, id));
    return id;
  }
  void clear() { store.clear(); }
};

std::string composite(char prefix, int num);

#endif // BACKENDS_BACKEND_HPP
