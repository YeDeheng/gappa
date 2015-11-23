/*
   Copyright (C) 2004 - 2013 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <iostream>
#include <fstream>
#include <list>
#include <map>
#include <typeinfo>
#include <set>
#include <string>
#include <vector>
#include "utils.hpp"
#include "backends/backend.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "parser/ast.hpp"
#include "parser/pattern.hpp"
#include "proofs/schemes.hpp"

extern std::string parameter_schemes;
extern backend *proof_generator;

bool is_unknown_theorem(char const *th)
{
  return proof_generator && !proof_generator->is_known(th);
}

typedef std::set< predicated_real > preal_set;
extern preal_set input_reals, output_reals;

struct scheme_factories: std::vector< scheme_factory const * > {
  ~scheme_factories() { for(iterator i = begin(), i_end = end(); i != i_end; ++i) delete *i; }
};

static static_ptr<scheme_factories> factories;

scheme_factory::scheme_factory(predicated_real const &r): target(r) {
  factories->push_back(this);
}

struct factorx_wrapper: scheme_factory {
  typedef factory_creator::factorx_fun factory_fun;
  factory_fun fun;
  factorx_wrapper(factory_fun f, predicated_real const &r)
  : scheme_factory(r), fun(f) {}
  virtual proof_scheme *operator()(predicated_real const &r, ast_real_vect const &h) const
  { return (*fun)(r, h); }
};

struct factory_wrapper: scheme_factory {
  typedef factory_creator::factory_fun factory_fun;
  factory_fun fun;
  factory_wrapper(factory_fun f)
  : scheme_factory(predicated_real()), fun(f) {}
  virtual proof_scheme *operator()(predicated_real const &r, ast_real_vect const &) const
  { return r.pred() == PRED_BND ? (*fun)(r.real()) : NULL; }
};

struct factorz_wrapper: scheme_factory {
  typedef factory_creator::factorz_fun factory_fun;
  factory_fun fun;
  factorz_wrapper(factory_fun f)
  : scheme_factory(predicated_real()), fun(f) {}
  virtual proof_scheme *operator()(predicated_real const &r, ast_real_vect const &) const
  { return (*fun)(r); }
};

factory_creator::factory_creator(factorx_fun f, predicated_real const &r)
{ new factorx_wrapper(f, r); }

factory_creator::factory_creator(factory_fun f)
{ new factory_wrapper(f); }

factory_creator::factory_creator(factorz_fun f)
{ new factorz_wrapper(f); }

typedef std::vector< proof_scheme const * > scheme_vect;
static scheme_vect source_schemes;

/** Timestamp for the currently running graph algorithm. Increased each time an algorithm starts. */
static unsigned visit_counter = 0;

typedef std::set< proof_scheme const * > scheme_set;
struct real_dependency
{
  scheme_set dependent;
  scheme_set schemes;
  mutable unsigned visited;
  real_dependency(): visited(0) {}
  bool can_visit() const;
};
typedef std::map< predicated_real, real_dependency > real_dependencies;
static real_dependencies reals;

typedef std::list< proof_scheme const * > scheme_list;

/**
 * Tells if the scheme has yet to be visited by the current graph algorithm.
 * In that case, the function updates the #visited timestamp so that the next call returns false.
 */
bool proof_scheme::can_visit() const
{
  if (visited == visit_counter) return false;
  visited = visit_counter;
  return true;
}

/**
 * Tells if the real has yet to be visited by the current graph algorithm.
 * In that case, the function updates the #visited timestamp so that the next call returns false.
 */
bool real_dependency::can_visit() const
{
  if (visited == visit_counter) return false;
  visited = visit_counter;
  return true;
}

/** Priority queue for storing schemes. */
struct scheme_queue
{
  static int const success = 50; /**< Score when successfully leaving #bad_queue. */
  void push(proof_scheme const *a);
  proof_scheme const *pop();
  scheme_list good_queue, bad_queue;
};

/**
 * Decreases the score of @a s and stores it in the corresponding queue.
 */
void scheme_queue::push(proof_scheme const *s)
{
  --s->score;
  if (s->score > 0) good_queue.push_back(s);
  else {
    s->score = 0;
    bad_queue.push_back(s);
  }
}

/**
 * Removes a scheme from #good_queue and returns it.
 * If the queue was empty, promotes #bad_queue to #good_queue first.
 */
proof_scheme const *scheme_queue::pop()
{
  if (good_queue.empty()) {
    if (bad_queue.empty()) return NULL;
    good_queue.swap(bad_queue);
  }
  proof_scheme const *s = good_queue.front();
  good_queue.pop_front();
  return s;
}

int stat_tested_real = 0, stat_discarded_real = 0,
    stat_tested_theo = 0, stat_discarded_theo = 0;

/**
 * Marks the source schemes as visited and puts them into @a v.
 */
static void initialize_scheme_list(scheme_queue &v)
{
  ++visit_counter;
  for (scheme_vect::const_iterator i = source_schemes.begin(),
       i_end = source_schemes.end(); i != i_end; ++i)
  {
    proof_scheme const *s = *i;
    s->visited = visit_counter;
    v.push(s);
  }
}

/**
 * Marks as visited and inserts into @a v all the schemes (except @a ss) that depend on @a real.
 */
static void insert_dependent(scheme_queue &v, predicated_real const &real, proof_scheme const *ss = NULL)
{
  scheme_set const &dep = reals[real].dependent;
  for (scheme_set::const_iterator i = dep.begin(),
       i_end = dep.end(); i != i_end; ++i)
  {
    proof_scheme const *s = *i;
    if (s == ss || !s->can_visit()) continue;
    if (s->hyp_cache) {
      unsigned l = s->needed_reals.size();
      for (unsigned j = 0; j != l && j < 32; ++j)
      {
        if (s->needed_reals[j] == real) s->hyp_cache &= ~(1u << j);
      }
      if (s->hyp_cache) { s->visited = 0; continue; }
    }
    v.push(s);
  }
}

static void delete_scheme(proof_scheme const *s, predicated_real const *restricted_real)
{
  // if there is a restriction, we are removing a scheme that depends on a real,
  // otherwise we are removing a scheme from a real; in both cases, we should
  // not modify the dependencies of this real
  preal_vect v = s->needed_reals;
  for(preal_vect::const_iterator i = v.begin(), end = v.end(); i != end; ++i) {
    predicated_real const &real = *i;
    if (restricted_real && real == *restricted_real) continue;
    reals[real].dependent.erase(s);
  }
  if (restricted_real) reals[s->real].schemes.erase(s);
  ++stat_discarded_theo;
  delete s;
}

static real_dependency &initialize_dependencies(predicated_real const &real)
{
  real_dependencies::iterator it = reals.find(real);
  if (it != reals.end()) return it->second;
  // no dependencies yet, let's generate them
  ++stat_tested_real;
  it = reals.insert(std::make_pair(real, real_dependency())).first;
  real_dependency &dep = it->second;
  scheme_set &l = dep.schemes;
  for (scheme_factories::iterator i = factories->begin(),
       i_end = factories->end(); i != i_end; ++i)
  {
    scheme_factory const &f = **i;
    ast_real_vect holders;
    if (f.target.null())
    {
      // no embedded pattern (or no hole left in the pattern, see below)
      no_hole:
      if (proof_scheme *s = f(real, holders)) l.insert(s);
      continue;
    }
    // there is an embedded pattern, match it against the current real
    if (f.target.pred() != real.pred()) continue;
    ast_real const *r1 = f.target.real(), *r2 = f.target.real2();
    if (!match(real.real(), r1, holders) ||
        (r2 && !match(real.real2(), r2, holders)))
      continue;
    // the embedded pattern is a match, try generating schemes
    if (holders.size() < 2 || (holders[0] && holders[1]))
      goto no_hole;
    assert(holders[0] || holders[1]);
    int p = !holders[1];
    // pattern position p is not filled, use approx/accurate pairs
    link_map const *lm = p ? &approximates : &accurates;
    link_map::const_iterator k = lm->find(holders[1 - p]);
    if (k == lm->end()) continue;
    ast_real_set const &s = k->second;
    for (ast_real_set::const_iterator j = s.begin(), j_end = s.end(); j != j_end; ++j) {
      holders[p] = *j;
      if (proof_scheme *s = f(real, holders)) l.insert(s);
    }
  }
  // create the dependencies
  for (scheme_set::const_iterator i = l.begin(), i_end = l.end(); i != i_end; ++i)
  {
    ++stat_tested_theo;
    proof_scheme const *s = *i;
    preal_vect v = s->needed_reals;
    for(preal_vect::const_iterator j = v.begin(), j_end = v.end(); j != j_end; ++j)
      initialize_dependencies(*j).dependent.insert(s);
  }
  return it->second;
}

typedef std::list< predicated_real > preal_list;

/**
 * Marks all the schemes and reals reachable from @a real.
 */
static void mark_dependent_schemes(predicated_real const &real)
{
  preal_list pending_reals;
  if (!reals[real].can_visit()) return;
  pending_reals.push_back(real);
  while (!pending_reals.empty())
  {
    predicated_real r = pending_reals.back();
    pending_reals.pop_back();
    scheme_set const &v = reals[r].dependent;
    for (scheme_set::const_iterator i = v.begin(), i_end = v.end(); i != i_end; ++i)
    {
      proof_scheme const *s = *i;
      if (!s || !s->can_visit()) continue;
      if (reals[s->real].can_visit()) pending_reals.push_back(s->real);
    }
  }
}

/**
 * Marks all the reals potentially useful for reaching @a real.
 */
static void mark_useful_reals(predicated_real const &real)
{
  preal_list pending_reals;
  if (!reals[real].can_visit()) return;
  pending_reals.push_back(real);
  while (!pending_reals.empty())
  {
    predicated_real r = pending_reals.back();
    pending_reals.pop_back();
    scheme_set const &v = reals[r].schemes;
    for (scheme_set::const_iterator i = v.begin(), i_end = v.end(); i != i_end; ++i)
    {
      proof_scheme const *s = *i;
      if (!s) continue;
      preal_vect w = s->needed_reals;
      for (preal_vect::const_iterator j = w.begin(), j_end = w.end(); j != j_end; ++j)
        if (reals[*j].can_visit()) pending_reals.push_back(*j);
    }
  }
}

/**
 * Generates all the schemes needed for linking inputs and outputs.
 */
preal_vect generate_proof_paths()
{
  // recursively search schemes needed for output reals
  for (preal_set::const_iterator i = output_reals.begin(),
       i_end = output_reals.end(); i != i_end; ++i)
  {
    real_dependency &r = initialize_dependencies(*i);
    r.dependent.insert(NULL);
  }
  // initialize hypothesis reals to handle contradictions
  for (preal_set::const_iterator i = input_reals.begin(),
       i_end = input_reals.end(); i != i_end; ++i)
  {
    real_dependency &r = initialize_dependencies(*i);
    r.schemes.insert(NULL);
    r.dependent.insert(NULL);
  }
  // find reachable schemes starting from source schemes and inputs, then remove unreachable schemes
  ++visit_counter;
  for (real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i)
  {
    real_dependency &r = i->second;
    for (scheme_set::iterator j = r.schemes.begin(), j_end = r.schemes.end(); j != j_end; ++j)
    {
      proof_scheme const *s = *j;
      if (!s || !s->needed_reals.empty()) continue;
      s->visited = visit_counter;
      mark_dependent_schemes(s->real);
    }
  }
  for (preal_set::const_iterator i = input_reals.begin(),
       i_end = input_reals.end(); i != i_end; ++i)
  {
    mark_dependent_schemes(*i);
  }
  for (real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i)
  {
    real_dependency &r = i->second;
    scheme_set v;
    v.swap(r.schemes);
    for (scheme_set::iterator j = v.begin(), j_end = v.end(); j != j_end; ++j)
    {
      proof_scheme const *s = *j;
      if (!s || s->visited == visit_counter) r.schemes.insert(s);
      else delete_scheme(s, NULL);
    }
  }
  // find reals reaching to outputs, then remove unneeded reals
  ++visit_counter;
  for (preal_set::const_iterator i = output_reals.begin(),
       i_end = output_reals.end(); i != i_end; ++i)
  {
    mark_useful_reals(*i);
  }
  for (preal_set::const_iterator i = input_reals.begin(),
       i_end = input_reals.end(); i != i_end; ++i)
  {
    mark_useful_reals(*i);
  }
  for (real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i)
  {
    real_dependency &r = i->second;
    if (r.visited == visit_counter) continue;
    for (scheme_set::iterator j = r.schemes.begin(), j_end = r.schemes.end(); j != j_end; ++j)
      if (*j) delete_scheme(*j, NULL);
    r.schemes.clear();
  }
  // remove reals without any scheme
  ++visit_counter;
  preal_list pending_reals;
  for (real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i)
  {
    if (!i->second.schemes.empty()) continue;
    pending_reals.push_back(i->first);
    i->second.visited = visit_counter;
  }
  while (!pending_reals.empty())
  {
    predicated_real real = pending_reals.back();
    pending_reals.pop_back();
    real_dependency &r = reals[real];
    for (scheme_set::const_iterator i = r.dependent.begin(),
         i_end = r.dependent.end(); i != i_end; ++i)
    {
      proof_scheme const *s = *i;
      if (!s) continue;
      predicated_real u = s->real;
      real_dependency const &t = reals[u];
      delete_scheme(s, &real);
      if (t.schemes.empty() && t.can_visit()) pending_reals.push_back(u);
    }
    reals.erase(real);
    ++stat_discarded_real;
  }
  // setup the source schemes now, and clean the dependencies
  for (real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i)
  {
    real_dependency &r = i->second;
    r.schemes.erase(NULL);
    for (scheme_set::iterator j = r.schemes.begin(), j_end = r.schemes.end(); j != j_end; ++j)
    {
      proof_scheme const *s = *j;
      if (s->needed_reals.empty())
        source_schemes.push_back(s);
    }
    r.dependent.erase(NULL);
  }
  // generate the scheme graph
  if (!parameter_schemes.empty())
  {
    std::ofstream out(parameter_schemes.c_str());
    out << "digraph {\n  node [shape=record];\n";
    for (real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i)
    {
      real_dependency &r = i->second;
      std::string var = dump_real(i->first);
      out << "  \"" << var << "\" [label=\"{";
      for (std::string::const_iterator j = var.begin(), j_end = var.end(); j != j_end; ++j)
      {
        switch (*j) {
          case '<': out << "&lt;"; break;
          case '>': out << "&gt;"; break;
          case '|': out << "&#124;"; break;
          default: out << *j;
        }
      }
      int num_th = 0;
      for (scheme_set::iterator j = r.schemes.begin(), j_end = r.schemes.end(); j != j_end; ++j)
        out << "|<" << ++num_th << '>' << typeid(**j).name();
      out << "}\"];\n";
      num_th = 0;
      for (scheme_set::iterator j = r.schemes.begin(), j_end = r.schemes.end(); j != j_end; ++j)
      {
        ++num_th;
        preal_vect v = (*j)->needed_reals;
        for (preal_vect::const_iterator k = v.begin(), k_end = v.end(); k != k_end; ++k)
          out << "  \"" << var << "\":" << num_th << " -> \"" << dump_real(*k) << "\";\n";
      }
    }
    out << "}\n";
    out.close();
  }
  // find unreachable outputs
  preal_vect missing_targets;
  for (preal_set::iterator i = output_reals.begin(),
       i_end = output_reals.end(); i != i_end; ++i)
  {
    real_dependencies::iterator j = reals.find(*i);
    if (j == reals.end())
      missing_targets.push_back(*i);
  }
  return missing_targets;
}

#ifdef LEAK_CHECKER
struct proof_paths_cleaner {
  ~proof_paths_cleaner();
};

proof_paths_cleaner::~proof_paths_cleaner() {
  for(real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i) {
    scheme_set &s = i->second.schemes;
    for(scheme_set::iterator j = s.begin(), j_end = s.end(); j != j_end; ++j)
      delete *j;
  }
}

static proof_paths_cleaner dummy;
#endif // LEAK_CHECKER

node *find_proof(property const &res, bool implies)
{
  node *n = find_proof(res.real);
  if (!n) return NULL;
  if (implies && !n->get_result().implies(res)) return NULL;
  if (!implies) {
    if (!res.real.pred_bnd()) return NULL;
    property p = n->get_result();
    p.intersect(res);
    if (!is_empty(p.bnd())) return NULL;
  }
  return n;
}

static bool fill_hypotheses(property *hyp, preal_vect const &v)
{
  for(preal_vect::const_iterator i = v.begin(), end = v.end(); i != end; ++i) {
    node *n = find_proof(*i);
    if (!n) return false;
    *(hyp++) = n->get_result();
  }
  return true;
}

int stat_tested_app = 0;

/**
 * Reduces disjunctions inside hypotheses given the knowledge of node @a n.
 */
static void reduce_hypotheses(node *n, std::list<logic_node *> &trees, logic_node *excluded, undefined_map *umap)
{
  std::list<logic_node *>::iterator i = trees.begin();
  while (i != trees.end())
  {
    if (*i == excluded) { ++i; continue; }
    property_tree t;
    bool changed;
    int v = (*i)->tree.try_simplify(n->get_result(), true, umap, changed, t);
    if (!v && !changed) { ++i; continue; }
    if ((v == 0 && changed) || v < 0) {
      logic_node *m = new logic_node(t, *i, n);
      if (v < 0) { top_graph->set_contradiction(m); return; }
      ++m->nb_good;
      trees.push_back(m);
    }
    (*i)->remove_known();
    i = trees.erase(i);
  }
}

static bool insert_atom(logic_node *n, property const &p, int i, std::list<logic_node *> &trees, property_tree &targets, scheme_queue *pending_schemes)
{
  if (!top_graph->try_property(p)) return false;
  //std::cerr << "Creating node for " << dump_property(p) << '\n';
  node *m = new logicp_node(p, n, i);
  top_graph->insert_node(m);
  if (top_graph->get_contradiction()) return true;
  if (!targets.empty() && targets.simplify(m->get_result()) < 0) return true;
  reduce_hypotheses(m, trees, n, NULL);
  if (top_graph->get_contradiction()) return true;
  if (pending_schemes) insert_dependent(*pending_schemes, p.real);
  return false;
}

/**
 * Repeatedly splits and reduces hypotheses.
 */
static bool split_hypotheses(std::list<logic_node *> &trees, property_tree &targets, scheme_queue *pending_schemes)
{
  restart:
  for (std::list<logic_node *>::iterator j = trees.begin(),
       j_end = trees.end(); j != j_end; ++j)
  {
    logic_node *n = *j;
    property_tree const &hyp = n->tree;
    assert(!hyp.empty());
    if (!hyp.conjunction) continue;
    if (!hyp.left) {
      if (insert_atom(n, *hyp.atom, 0, trees, targets, pending_schemes))
        return true;
    } else for (int i = 0; i != 2; ++i)
    {
      property_tree const *t = i ? hyp.right : hyp.left;
      if (t->left || !t->conjunction) {
        logic_node *m = new logic_node(*t, n, i + 1);
        ++m->nb_good;
        trees.push_back(m);
      } else if (insert_atom(n, *t->atom, i + 1, trees, targets, pending_schemes))
        return true;
    }
    n->remove_known();
    trees.erase(j);
    goto restart;
  }
  return false;
}

/**
 * Fills this graph by iteratively applying theorems until
 * \li @a targets are satisfied, or
 * \li a contradiction is found, or
 * \li a fixpoint is reached for the results, or
 * \li an upper bound on the number of iterations is reached.
 */
void graph_t::populate(property_tree const &targets,
  dichotomy_sequence const &dichotomy, int iter_max, undefined_map *umap)
{
  if (contradiction) return;
  iter_max = iter_max / (2 * dichotomy.size() + 1);
  property_tree current_targets = targets;
  graph_loader loader(this);

  if (split_hypotheses(trees, current_targets, NULL)) return;

  for (dichotomy_sequence::const_iterator dichotomy_it = dichotomy.begin(),
       dichotomy_end = dichotomy.end(); /*nothing*/; ++dichotomy_it)
  {
    scheme_queue missing_schemes;
    initialize_scheme_list(missing_schemes);
    int iter = 0;
    for (node_map::const_iterator i = known_reals.begin(),
         i_end = known_reals.end(); i != i_end; ++i)
    {
      if (i->first.pred_bnd() && !is_bounded(i->second->get_result().bnd())) continue;
      insert_dependent(missing_schemes, i->first);
      --iter;
    }
    proof_scheme const *s;
    while (iter++ != iter_max && ((s = missing_schemes.pop())))
    {
      s->visited = 0; // allows the scheme to be reused later, if needed
      ++stat_tested_app;
      property hyps[s->needed_reals.size()];
      if (!fill_hypotheses(hyps, s->needed_reals)) {
        // The scheme is missing some hypotheses.
        continue;
      }
      property res(s->real);
      std::string name = s->default_name;
      s->compute(hyps, res, name);
      if (res.null() || (res.real.pred_bnd() && !is_defined(res.bnd()))) {
        // The scheme failed.
        continue;
      }
      if (!try_property(res))
      {
        // The scheme did not find anything new.
        continue;
      }
      //std::cerr << dump_property(res) << '\t' << name << '\n';
      node *n = create_theorem(s->needed_reals.size(), hyps, res, name, s);
      insert_node(n);
      if (!s->score) s->score = scheme_queue::success;
      if (contradiction) {
        // We have got a contradiction, everything is true.
        return;
      }
      insert_dependent(missing_schemes, s->real, s);
      reduce_hypotheses(n, trees, NULL, NULL);
      if (contradiction) return;
      if (split_hypotheses(trees, current_targets, &missing_schemes)) return;
      if (!current_targets.empty() && current_targets.simplify(n->get_result()) < 0) return;
    }
    if (iter > iter_max)
      std::cerr << "Warning: maximum number of iterations reached.\n";
    if (dichotomy_it != dichotomy_end) {
      dichotomize(*dichotomy_it, iter_max);
      if (contradiction) return;
    }
    for (node_map::const_iterator i = known_reals.begin(),
         i_end = known_reals.end(); i != i_end; ++i)
    {
      if (i->first.pred_bnd() && !is_bounded(i->second->get_result().bnd())) continue;
      reduce_hypotheses(i->second, trees, NULL, dichotomy_it != dichotomy_end ? NULL : umap);
      if (contradiction) return;
    }
    if (dichotomy_it == dichotomy_end) {
      static ast_real_set already;
      splitting s;
      for (std::list<logic_node *>::const_iterator i = trees.begin(),
           i_end = trees.end(); i != i_end; ++i)
      {
        (*i)->tree.get_splitting(s);
      }
      unsigned max_pts = 0;
      splitting::value_type const *sv = NULL;
      for (splitting::const_iterator i = s.begin(), i_end = s.end(); i != i_end; ++i)
      {
        if (i->first.real2() || i->second.size() <= max_pts ||
            already.find(i->first.real()) != already.end())
          continue;
        node *n = find_proof(i->first.real());
        if (!n || is_singleton(n->get_result().bnd())) continue;
        max_pts = i->second.size();
        sv = &*i;
      }
      if (max_pts <= 1) goto fill_holes;
      ast_real_set save = already;
      unsigned long ds = 0;
      number prev = number::neg_inf;
      for (split_point_mset::const_iterator i = sv->second.begin(),
           i_end = sv->second.end(); i != i_end; ++i)
      {
        if (i->pt == prev) continue;
        ds = fill_splitter(ds, *i);
        prev = i->pt;
      }
      already.insert(sv->first.real());
      dichotomy_var dv = { sv->first.real(), ds };
      dichotomy_hint dh = { dvar_vect(1, dv), property_tree() };
      dichotomize(dh, iter_max);
      already = save;
      goto fill_holes;
    }
    if (split_hypotheses(trees, current_targets, &missing_schemes)) return;
  }

  fill_holes:
  if (!umap) return;
  for (node_map::const_iterator i = known_reals.begin(),
       i_end = known_reals.end(); i != i_end; ++i)
  {
    if (i->first.pred_bnd() && !is_bounded(i->second->get_result().bnd())) continue;
    reduce_hypotheses(i->second, trees, NULL, umap);
    if (contradiction) return;
  }
}
