/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#ifndef PROOFS_UPDATER_HPP
#define PROOFS_UPDATER_HPP

#include "proofs/proof_graph.hpp"


property boundify(property const &opt, property const &cur);

void expand(theorem_node *n, property const &p);

#endif // PROOFS_UPDATER_HPP
