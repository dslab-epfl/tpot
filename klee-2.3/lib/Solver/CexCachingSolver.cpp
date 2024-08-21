//===-- CexCachingSolver.cpp ----------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Solver/Solver.h"

#include "klee/ADT/MapOfSets.h"
#include "klee/Expr/Assignment.h"
#include "klee/Expr/Constraints.h"
#include "klee/Expr/Expr.h"
#include "klee/Expr/ExprUtil.h"
#include "klee/Expr/ExprVisitor.h"
#include "klee/Support/OptionCategories.h"
#include "klee/Statistics/TimerStatIncrementer.h"
#include "klee/Solver/SolverImpl.h"
#include "klee/Solver/SolverStats.h"
#include "klee/Support/ErrorHandling.h"

#include "llvm/Support/CommandLine.h"

using namespace klee;
using namespace llvm;

namespace {
cl::opt<bool> DebugCexCacheCheckBinding(
    "debug-cex-cache-check-binding", cl::init(false),
    cl::desc("Debug the correctness of the counterexample "
             "cache assignments (default=false)"),
    cl::cat(SolvingCat));

cl::opt<bool>
    CexCacheTryAll("cex-cache-try-all", cl::init(false),
                   cl::desc("Try substituting all counterexamples before "
                            "asking the SMT solver (default=false)"),
                   cl::cat(SolvingCat));

cl::opt<bool>
    CexCacheSuperSet("cex-cache-superset", cl::init(false),
                     cl::desc("Try substituting SAT superset counterexample "
                              "before asking the SMT solver (default=false)"),
                     cl::cat(SolvingCat));

cl::opt<bool> CexCacheExperimental(
    "cex-cache-exp", cl::init(false),
    cl::desc("Optimization for validity queries (default=false)"),
    cl::cat(SolvingCat));

} // namespace

///

typedef std::set< ref<Expr> > KeyType;

struct AssignmentLessThan {
  bool operator()(const Assignment *a, const Assignment *b) const {
    return a->arr_bindings < b->arr_bindings;
  }
};


class CexCachingSolver : public SolverImpl {
  typedef std::set<Assignment*, AssignmentLessThan> assignmentsTable_ty;

  Solver *solver;
  
  MapOfSets<ref<Expr>, Assignment*> cache;
  // memo table
  assignmentsTable_ty assignmentsTable;

  bool searchForAssignment(KeyType &key, 
                           Assignment *&result);
  
  bool lookupAssignment(const Query& query, KeyType &key, Assignment *&result);

  bool lookupAssignment(const Query& query, Assignment *&result) {
    KeyType key;
    return lookupAssignment(query, key, result);
  }

  bool getAssignment(const Query& query, Assignment *&result);
  
public:
  CexCachingSolver(Solver *_solver) : solver(_solver) {}
  ~CexCachingSolver();
  
  bool computeTruth(const Query&, bool &isValid);
  bool computeValidity(const Query&, Solver::Validity &result);
  bool computeValue(const Query&, ref<Expr> &result);
  bool computeInitialValues(const Query &query,
                            const std::vector<const Array *> &arr_objects,
                            std::vector<std::vector<unsigned char> > &arr_values,
                            const std::vector<const BitVecExpr *> &bv_objects,
                            std::vector<bitvec_ce_t> &bv_values,
                            const std::vector<const IntExpr *> &int_objects,
                            std::vector<int_ce_t> &int_values,  
                            bool &hasSolution);
  SolverRunStatus getOperationStatusCode();
  char *getConstraintLog(const Query& query);
  void setCoreSolverTimeout(time::Span timeout);
};

///

struct NullAssignment {
  bool operator()(Assignment *a) const { return !a; }
};

struct NonNullAssignment {
  bool operator()(Assignment *a) const { return a!=0; }
};

struct NullOrSatisfyingAssignment {
  KeyType &key;
  
  NullOrSatisfyingAssignment(KeyType &_key) : key(_key) {}

  bool operator()(Assignment *a) const { 
    return !a || a->satisfies(key.begin(), key.end()); 
  }
};

/// searchForAssignment - Look for a cached solution for a query.
///
/// \param key - The query to look up.
/// \param result [out] - The cached result, if the lookup is successful. This is
/// either a satisfying assignment (for a satisfiable query), or 0 (for an
/// unsatisfiable query).
/// \return - True if a cached result was found.
bool CexCachingSolver::searchForAssignment(KeyType &key, Assignment *&result) {
  Assignment * const *lookup = cache.lookup(key);
  if (lookup) {
    result = *lookup;
    return true;
  }

  if (CexCacheTryAll) {
    // Look for a satisfying assignment for a superset, which is trivially an
    // assignment for any subset.
    Assignment **lookup = 0;
    if (CexCacheSuperSet)
      lookup = cache.findSuperset(key, NonNullAssignment());

    // Otherwise, look for a subset which is unsatisfiable, see below.
    if (!lookup) 
      lookup = cache.findSubset(key, NullAssignment());

    // If either lookup succeeded, then we have a cached solution.
    if (lookup) {
      result = *lookup;
      return true;
    }

    // Otherwise, iterate through the set of current assignments to see if one
    // of them satisfies the query.
    for (assignmentsTable_ty::iterator it = assignmentsTable.begin(), 
           ie = assignmentsTable.end(); it != ie; ++it) {
      Assignment *a = *it;
      if (a->satisfies(key.begin(), key.end())) {
        result = a;
        return true;
      }
    }
  } else {
    // FIXME: Which order? one is sure to be better.

    // Look for a satisfying assignment for a superset, which is trivially an
    // assignment for any subset.
    Assignment **lookup = 0;
    if (CexCacheSuperSet)
      lookup = cache.findSuperset(key, NonNullAssignment());

    // Otherwise, look for a subset which is unsatisfiable -- if the subset is
    // unsatisfiable then no additional constraints can produce a valid
    // assignment. While searching subsets, we also explicitly the solutions for
    // satisfiable subsets to see if they solve the current query and return
    // them if so. This is cheap and frequently succeeds.
    if (!lookup) 
      lookup = cache.findSubset(key, NullOrSatisfyingAssignment(key));

    // If either lookup succeeded, then we have a cached solution.
    if (lookup) {
      result = *lookup;
      return true;
    }
  }
  
  return false;
}

/// lookupAssignment - Lookup a cached result for the given \arg query.
///
/// \param query - The query to lookup.
/// \param key [out] - On return, the key constructed for the query.
/// \param result [out] - The cached result, if the lookup is successful. This is
/// either a satisfying assignment (for a satisfiable query), or 0 (for an
/// unsatisfiable query).
/// \return True if a cached result was found.
bool CexCachingSolver::lookupAssignment(const Query &query, 
                                        KeyType &key,
                                        Assignment *&result) {
  key = KeyType(query.constraints.begin(), query.constraints.end());
  ref<Expr> neg = Expr::createIsZero(query.expr);
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(neg)) {
    if (CE->isFalse()) {
      result = (Assignment*) 0;
      ++stats::queryCexCacheHits;
      return true;
    }
  } else {
    key.insert(neg);
  }

  bool found = searchForAssignment(key, result);
  if (found)
    ++stats::queryCexCacheHits;
  else ++stats::queryCexCacheMisses;
    
  return found;
}

bool CexCachingSolver::getAssignment(const Query& query, Assignment *&result) {
  KeyType key;
  if (lookupAssignment(query, key, result))
    return true;

  std::vector<const Array*> arr_objects;
  std::vector<const BitVecExpr*> bv_objects;
  std::vector<const IntExpr*> int_objects;
  findSymbolicObjects(key.begin(), key.end(), arr_objects, bv_objects, int_objects);

  std::vector< std::vector<unsigned char> > arr_values;
  std::vector<bitvec_ce_t> bv_values;
  std::vector<int_ce_t> int_values;
  bool hasSolution;
  if (!solver->impl->computeInitialValues(query, arr_objects, arr_values,
                                          bv_objects, bv_values,
                                          int_objects, int_values,
                                          hasSolution))
    return false;
    
  Assignment *binding;
  if (hasSolution) {
    // TODO: handle bitvector bindings
    binding = new Assignment(arr_objects, arr_values, bv_objects, bv_values, int_objects, int_values);

    // Memoize the result.
    std::pair<assignmentsTable_ty::iterator, bool>
      res = assignmentsTable.insert(binding);
    if (!res.second) {
      delete binding;
      binding = *res.first;
    }
    
    if (DebugCexCacheCheckBinding)
      if (!binding->satisfies(key.begin(), key.end())) {
        query.dump();
        binding->dump();
        klee_error("Generated assignment doesn't match query");
      }
  } else {
    binding = (Assignment*) 0;
  }
  
  result = binding;
  cache.insert(key, binding);

  return true;
}

///

CexCachingSolver::~CexCachingSolver() {
  cache.clear();
  delete solver;
  for (assignmentsTable_ty::iterator it = assignmentsTable.begin(), 
         ie = assignmentsTable.end(); it != ie; ++it)
    delete *it;
}

bool CexCachingSolver::computeValidity(const Query& query,
                                       Solver::Validity &result) {
  TimerStatIncrementer t(stats::cexCacheTime);
  Assignment *a;
  if (!getAssignment(query.withFalse(), a))
    return false;
  assert(a && "computeValidity() must have assignment");
  ref<Expr> q = a->evaluate(query.expr);
  assert(isa<ConstantExpr>(q) && 
         "assignment evaluation did not result in constant");

  if (cast<ConstantExpr>(q)->isTrue()) {
    if (!getAssignment(query, a))
      return false;
    result = !a ? Solver::True : Solver::Unknown;
  } else {
    if (!getAssignment(query.negateExpr(), a))
      return false;
    result = !a ? Solver::False : Solver::Unknown;
  }
  
  return true;
}

bool CexCachingSolver::computeTruth(const Query& query,
                                    bool &isValid) {
  TimerStatIncrementer t(stats::cexCacheTime);

  // There is a small amount of redundancy here. We only need to know
  // truth and do not really need to compute an assignment. This means
  // that we could check the cache to see if we already know that
  // state ^ query has no assignment. In that case, by the validity of
  // state, we know that state ^ !query must have an assignment, and
  // so query cannot be true (valid). This does get hits, but doesn't
  // really seem to be worth the overhead.

  if (CexCacheExperimental) {
    Assignment *a;
    if (lookupAssignment(query.negateExpr(), a) && !a)
      return false;
  }

  Assignment *a;
  if (!getAssignment(query, a))
    return false;

  isValid = !a;

  return true;
}

bool CexCachingSolver::computeValue(const Query& query,
                                    ref<Expr> &result) {
  TimerStatIncrementer t(stats::cexCacheTime);

  Assignment *a;
  if (!getAssignment(query.withFalse(), a))
    return false;
  assert(a && "computeValue() must have assignment");
  result = a->evaluate(query.expr);  
  assert(isa<ConstantExpr>(result) && 
         "assignment evaluation did not result in constant");
  return true;
}

bool 
CexCachingSolver::computeInitialValues(const Query &query,
                            const std::vector<const Array *> &arr_objects,
                            std::vector<std::vector<unsigned char> > &arr_values,
                            const std::vector<const BitVecExpr *> &bv_objects,
                            std::vector<bitvec_ce_t> &bv_values,
                            const std::vector<const IntExpr *> &int_objects,
                            std::vector<int_ce_t> &int_values,  
                            bool &hasSolution) {
  TimerStatIncrementer t(stats::cexCacheTime);
  Assignment *a;
  if (!getAssignment(query, a))
    return false;
  hasSolution = !!a;
  
  if (!a)
    return true;

  // FIXME: We should use smarter assignment for result so we don't
  // need redundant copy.
  arr_values = std::vector< std::vector<unsigned char> >(arr_objects.size());
  for (unsigned i=0; i < arr_objects.size(); ++i) {
    const Array *os = arr_objects[i];
    Assignment::array_bindings_ty::iterator it = a->arr_bindings.find(os);
    if (it == a->arr_bindings.end()) {
      arr_values[i] = std::vector<unsigned char>(os->size, 0);
    } else {
      arr_values[i] = it->second;
    }
  }

  bv_values = std::vector<bitvec_ce_t>(bv_objects.size());
  for (unsigned i=0; i < bv_objects.size(); ++i) {
    const BitVecExpr *os = bv_objects[i];
    Assignment::bitvec_bindings_ty::iterator it = a->bv_bindings.find(os);
    if (it == a->bv_bindings.end()) {
      // assert(0 && "looking for more objects than are available in assignment");
      // The counterexample cache needs this to check assignments generated before
      // extra symbolic arrays and bvs have been created.
      // (parallel to Assignment::evaluate(BitVecExpr *))
      bv_values[i] = 0;
    } else {
      bv_values[i] = it->second;
    }
  }

  // TODO: copied and pasted this from the bv counterpart without considering if we need changes.
  int_values = std::vector<int_ce_t>(int_objects.size());
  for (unsigned i=0; i < int_objects.size(); ++i) {
    const IntExpr *os = int_objects[i];
    Assignment::int_bindings_ty::iterator it = a->int_bindings.find(os);
    if (it == a->int_bindings.end()) {
      // assert(0 && "looking for more objects than are available in assignment");
      // The counterexample cache needs this to check assignments generated before
      // extra symbolic arrays and bvs have been created.
      // (parallel to Assignment::evaluate(BitVecExpr *))
      int_values[i] = 0;
    } else {
      int_values[i] = it->second;
    }
  }
  
  return true;
}

SolverImpl::SolverRunStatus CexCachingSolver::getOperationStatusCode() {
  return solver->impl->getOperationStatusCode();
}

char *CexCachingSolver::getConstraintLog(const Query& query) {
  return solver->impl->getConstraintLog(query);
}

void CexCachingSolver::setCoreSolverTimeout(time::Span timeout) {
  solver->impl->setCoreSolverTimeout(timeout);
}

///

Solver *klee::createCexCachingSolver(Solver *_solver) {
  return new Solver(new CexCachingSolver(_solver));
}
