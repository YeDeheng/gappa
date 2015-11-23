/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <iostream>

#include "papi.h"
#include "parameters.hpp"
#include "backends/backend.hpp"
#include "numbers/interval_utility.hpp"
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/schemes.hpp"

extern bool parameter_constrained, parameter_statistics;
extern int yyparse(void);
extern bool detailed_io;
extern backend *proof_generator;
dichotomy_sequence dichotomies;
property_tree context;

extern int
  stat_tested_real, stat_discarded_real,
  stat_tested_theo, stat_discarded_theo,
  stat_tested_app, stat_successful_app,
  stat_intersected_pred, stat_discarded_pred;

int main(int argc, char **argv)
{
    long long start_time, end_time; 
    PAPI_library_init(PAPI_VER_CURRENT);
    start_time = PAPI_get_real_usec();

  parse_args_status pargs_status = parse_args(argc, argv);
  if (pargs_status != PARGS_CONTINUE)
    return pargs_status == PARGS_FAILURE ? EXIT_FAILURE : EXIT_SUCCESS;
  if (proof_generator) {
    if (!parameter_constrained) {
      std::cerr << "Error: unconstrained mode is not compatible with script generation, since proofs are left incomplete.\n";
      return EXIT_FAILURE;
    }
    proof_generator->initialize(std::cout);
  }
  if (yyparse()) return EXIT_FAILURE;
  preal_vect missing_paths = generate_proof_paths();
  for (preal_vect::const_iterator i = missing_paths.begin(),
       i_end = missing_paths.end(); i != i_end; ++i)
  {
    std::cerr << "Warning: no path was found for " << dump_real(*i) << ".\n";
  }
  bool globally_proven = true;
  undefined_map umap;
  graph_t *g = new graph_t(NULL, context);
  g->populate(property_tree(), dichotomies, 100*1000*1000, &umap);
  if (!umap.empty()) {
    std::cerr << "Results:\n";
    for (undefined_map::const_iterator i = umap.begin(),
         i_end = umap.end(); i != i_end; ++i)
    {
      change_io_format dummy(IO_APPROX);
      std::cerr << "  " << dump_property_nice(i->second) << '\n';
    }
  }
  if (node *n = g->get_contradiction()) {
    if (proof_generator) {
      enlarger(node_vect(1, n));
      instances = &umap;
      proof_generator->theorem(n);
    }
  } else {
    g->show_negative();
    globally_proven = false;
  }
  g->show_dangling();
  delete g;
  if (proof_generator) proof_generator->finalize();
  if (parameter_statistics) {
    std::cerr <<
      "Statistics:\n"
      "  " << stat_tested_real << " expressions were considered,\n"
      "    but then " << stat_discarded_real << " of those got discarded.\n"
      "  " << stat_tested_theo << " theorems were considered,\n"
      "    but then " << stat_discarded_theo << " of those got discarded.\n"
      "  " << stat_tested_app << " applications were tried. Among those,\n"
      "    " << stat_successful_app << " were successful,\n"
      "    yet " << stat_discarded_pred << " proved useless\n"
      "    and " << stat_intersected_pred << " improved existing results.\n";
  }

  // PAPI time measure, added by Deheng
  end_time = PAPI_get_real_usec();
  std::cerr << "Time measured by PAPI is : " <<  end_time - start_time << " us" << std::endl; 


  return globally_proven ? EXIT_SUCCESS : EXIT_FAILURE;
}
