/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <cstdlib>
#include <iostream>
#include <string>

#include "../config.h"
#include "parameters.hpp"
#include "backends/backend.hpp"

int parameter_internal_precision = 60;
int parameter_dichotomy_depth = 100;
bool parameter_rfma = false;
bool parameter_constrained = true;
bool parameter_statistics = false;
std::string parameter_schemes;
bool warning_dichotomy_failure = true;
bool warning_hint_difference = true;
bool warning_null_denominator = true;
bool warning_unbound_variable = true;
backend *proof_generator = NULL;

static void help() {
  std::cerr <<
    "Usage: gappa [OPTIONS] [FILE]\n"
    "Read a statement on standard input and display its proof on standard output.\n"
    "\n"
    "  -h, --help                      display this help and exit\n"
    "  -v, --version                   output version information and exit\n"
    "\n"
    "Engine parameters:\n"
    "  -Eprecision=int                 internal precision (default: " << parameter_internal_precision << ")\n"
    "  -Edichotomy=int                 dichotomy depth (default: " << parameter_dichotomy_depth << ")\n"
    "  -E[no-]reverted-fma             change fma(a,b,c) from a*b+c to c+a*b\n"
    "\n"
    "Engine modes:\n"
    "  -Munconstrained                 do not check for theorem constraints\n"
    "  -Mstatistics                    display statistics\n"
    "  -Mschemes[=FILE]                produce a dot graph (default: schemes.dot)\n"
    "\n"
    "Warnings: (default: all)\n"
    "  -W[no-]dichotomy-failure\n"
    "  -W[no-]hint-difference\n"
    "  -W[no-]null-denominator\n"
    "  -W[no-]unbound-variable\n"
    "\n"
    "Backend:\n"
    "  -Bnull                          do not generate a proof (default)\n"
    "  -Bcoq                           produce a script for the Coq proof checker\n"
    "  -Bcoq-lambda                    produce a term for the Coq proof checker\n"
    "  -Blatex                         produce a LaTeX text\n";
}

extern void change_input(std::string const &n);

bool parse_option(std::string const &s, bool embedded)
{
  static bool no_more_options = false;
  if (s.size() < 2 || s[0] != '-' || (!embedded && no_more_options))
  {
    static bool already_done = false;
    if (embedded || already_done) return false;
    change_input(s);
    already_done = true;
    return true;
  }
  if (!embedded && s == "--")
  {
    no_more_options = true;
    return true;
  }
  switch (s[1]) {
  case 'E': {
    std::string::size_type p = s.find('=');
    if (p == std::string::npos) {
      bool yes = s.size() <= 6 || s.substr(2, 3) != "no-";
      std::string o = s.substr(yes ? 2 : 5);
      if (o == "reverted-fma") parameter_rfma = yes;
      else return false;
    } else {
      std::string o = s.substr(2, p - 2), v = s.substr(p + 1);
      int *param;
      if (o == "precision") param = &parameter_internal_precision; else
      if (o == "dichotomy") param = &parameter_dichotomy_depth;
      else return false;
      *param = atoi(v.c_str()); 
    }
    break; }
  case 'M': {
    if (embedded) return false;
    std::string o = s.substr(2);
    if (o == "unconstrained") parameter_constrained   = false; else
    if (o == "statistics"   ) parameter_statistics    = true; else
    if (o.compare(0, 7, "schemes") == 0)
    {
      if (o.size() == 7) parameter_schemes = "schemes.dot";
      else
      {
        if (o[7] != '=') return false;
        parameter_schemes = o.substr(8);
      }
    }
    else return false;
    break;
  }
  case 'W': {
    bool yes = s.size() <= 6 || s.substr(2, 3) != "no-";
    std::string o = s.substr(yes ? 2 : 5);
    if (o == "dichotomy-failure") warning_dichotomy_failure = yes; else
    if (o == "hint-difference"  ) warning_hint_difference   = yes; else
    if (o == "null-denominator" ) warning_null_denominator  = yes; else
    if (o == "unbound-variable" ) warning_unbound_variable  = yes;
    else return false;
    break; }
  case 'B': {
    if (embedded) return false;
    std::string o = s.substr(2);
    if (o == "null") proof_generator = NULL;
    else {
      proof_generator = backend::find(o);
      if (!proof_generator) return false;
    }
    break; }
  default:
    return false;
  }
  return true;
}

parse_args_status parse_args(int argc, char **argv)
{
  for (int i = 1; i < argc; ++i)
  {
    std::string s = argv[i];
    if (parse_option(s, false)) continue;
    if (s == "-v" || s == "--version") {
      std::cout << PACKAGE_STRING << '\n';
      return PARGS_EXIT;
    }
    if (s == "-h" || s == "--help") {
      help();
      return PARGS_EXIT;
    }
    std::cerr << "Error: unrecognized option '" << s << "'.\n\n";
    help();
    return PARGS_FAILURE;
  }
  return PARGS_CONTINUE;
}
