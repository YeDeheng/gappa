/*
   Copyright (C) 2004 - 2013 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#ifndef PROOFS_SCHEMES_HPP
#define PROOFS_SCHEMES_HPP

#include "parser/ast_real.hpp"
#include "proofs/proof_graph.hpp"

typedef std::vector< predicated_real > preal_vect;

enum update
{
  UPD_TRIV, //< Result is enlarged, hypotheses are unchanged.
  UPD_COPY, //< Result is enlarged and copied to the last hypothesis.
  UPD_SEEK, //< Result and hypotheses are enlarged.
};

/**
 * Abstract interface for a theorem instance.
 * \li It stores the complete predicates used in the goal and the hypotheses.
 * \li It checks the validity of the filled hypotheses, it performs
 *     numerical computations to fill the goal, and it generates the
 *     corresponding proof node.
 */
struct proof_scheme
{
  /**
   * Fills @a res with the property deduced from @a hyps, and sets @a name with
   * the corresponding theorem.
   * @note @a res should be initialized with #real, @a hyps should match
   *       #needed_reals, and @a name should be initialized with #default_name.
   */
  virtual void compute(property const hyps[], property &res, std::string &name) const = 0;
  virtual ~proof_scheme() {}
  /** Initializes the scheme with the structure of the goal and hypotheses. */
  proof_scheme(predicated_real const &r, preal_vect const &n, char const *d, update u = UPD_SEEK)
    : real(r), needed_reals(n), default_name(d), update_kind(u), visited(0),
      hyp_cache(n.size() < 31 ? (1u << n.size()) - 1 : 0), score(0) {}
  const predicated_real real; //< Predicate of the goal.
  const preal_vect needed_reals; //< Predicates of the hypotheses.
  std::string default_name; //< Default name of the generator.
  update update_kind;
  mutable unsigned visited;
  bool can_visit() const;
  mutable unsigned hyp_cache;
  mutable int score;
};

/**
 * Abstract interface for generating a theorem instance (proof_scheme)
 * able to produce a property about predicate #target.
 */
struct scheme_factory
{
  /**
   * Predicate with holes.
   * The predicate might be left empty for a very generic factory that
   * intends to be called for any predicate and does not care about
   * approximate/accurate pattern resolution.
   */
  const predicated_real target;
  /** Initializes the factory with its target predicate. Registers it globally. */
  scheme_factory(predicated_real const &r);
  /**
   * Generates a theorem instance for target predicate @a r, which is filled
   * by the values in @a holes.
   * @return NULL if the theorem is not worth applying to this target,
   *         e.g. a more precise one exists.
   */
  virtual proof_scheme *operator()(predicated_real const &r, ast_real_vect const &holes) const = 0;
  virtual ~scheme_factory() {}
};

/**
 * Helper class for creating a theorem generator (scheme_factory) from a
 * free function (usually a static member of a proof_scheme descendant).
 */
struct factory_creator {
  typedef proof_scheme *(*factorx_fun)(predicated_real const &, ast_real_vect const &);
  typedef proof_scheme *(*factory_fun)(ast_real const *);
  typedef proof_scheme *(*factorz_fun)(predicated_real const &);
  factory_creator(factorx_fun f, predicated_real const &);
  factory_creator(factory_fun f);
  factory_creator(factorz_fun f);
};

#define REGISTER_SCHEME_BEGIN(name) \
  class name##_scheme: proof_scheme { \
    virtual void compute(property const [], property &, std::string &) const

#define REGISTER_SCHEME_END(name) \
   public: \
    static proof_scheme *factory(ast_real const *); \
  }; \
  static factory_creator name##_scheme_register(&name##_scheme::factory)

#define REGISTER_SCHEME_END_PREDICATE(name) \
   public: \
    static proof_scheme *factory(predicated_real const &); \
  }; \
  static factory_creator name##_scheme_register(&name##_scheme::factory)

#define REGISTER_SCHEME_END_PATTERN(name, pattern) \
   public: \
    static proof_scheme *factory(predicated_real const &, ast_real_vect const &); \
  }; \
  static factory_creator name##_scheme_register(&name##_scheme::factory, pattern)

inline node *find_proof(predicated_real const &real)
{ return top_graph->find_already_known(real); }
node *find_proof(property const &, bool = true);

preal_vect generate_proof_paths();

/** Returns true if the theorem is unknown by the current back-end. */
bool is_unknown_theorem(const char *);

#endif // PROOFS_SCHEMES_HPP
