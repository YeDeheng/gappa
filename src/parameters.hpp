/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#ifndef PARAMETERS_HPP
#define PARAMETERS_HPP

#include <string>

enum parse_args_status {
  PARGS_CONTINUE, PARGS_EXIT, PARGS_FAILURE
};

/**
 * Parses an option found on the command-line or in the input script.
 *
 * @param embedded true if the option comes from the input script
 * @return false when option @a s is not recognized.
 */
bool parse_option(std::string const &s, bool embedded);

/**
 * Parses the command-line arguments.
 */
parse_args_status parse_args(int argc, char **argv);

#endif // PARAMETERS_HPP
