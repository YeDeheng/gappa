/*
   Copyright (C) 2004 - 2012 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <iosfwd>
#include <map>
#include <string>

class ast_real;
class interval;
class number;
class predicated_real;
class property;
class property_tree;
class property_vect;
class theorem_node;

namespace coq {

typedef std::map<std::string, std::string> theorem_map;
typedef std::map< predicated_real, std::pair< int, property const * > > property_map;

extern theorem_map theorems;

/** Use fully-qualified names for Coq identifiers. */
extern bool fqn;

/** Use vernacular for definitions. */
extern bool vernac;

/** Output stream for global variables. */
extern std::ostream *out_vars;

std::string convert_name(std::string const &name);
std::string display(number const &f);
std::string display(interval const &i);
std::string display(ast_real const *r);
std::string display(property const &p);
std::string display(property_tree const &p);
std::string display(theorem_node *t);
std::string display(node *n);

void apply_theorem(auto_flush &plouf, std::string const &th,
                   property const &res, property const *hyp,
                   property_map const *pmap = NULL, int *num = NULL);

std::string subset_name(property const &p1, property const &p2);
void invoke_lemma(auto_flush &plouf, property_vect const &hyp, property_map const &pmap);
void invoke_lemma(auto_flush &plouf, node *n, property_map const &pmap);
void reset();
bool known_theorem(std::string const &);

}
