//===-- ValidatingSolver.cpp ----------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Expr/Constraints.h"
#include "klee/Solver/Solver.h"
#include "klee/Solver/SolverImpl.h"

#include <vector>

namespace klee {

class ValidatingSolver : public SolverImpl {
private:
  Solver *solver, *oracle;

public:
  ValidatingSolver(Solver *_solver, Solver *_oracle)
      : solver(_solver), oracle(_oracle) {}
  ~ValidatingSolver() { delete solver; }

  bool computeValidity(const Query &, Solver::Validity &result);
  bool computeTruth(const Query &, bool &isValid);
  bool computeValue(const Query &, ref<Expr> &result);
  bool computeInitialValues(const Query &query,
                            const std::vector<const Array *> &arr_objects,
                            std::vector<std::vector<unsigned char> > &arr_values,
                            const std::vector<const BitVecExpr *> &bv_objects,
                            std::vector<bitvec_ce_t> &bv_values,
                            const std::vector<const IntExpr *> &int_objects,
                            std::vector<int_ce_t> &int_values,  
                            bool &hasSolution);
  SolverRunStatus getOperationStatusCode();
  char *getConstraintLog(const Query &);
  void setCoreSolverTimeout(time::Span timeout);
};

bool ValidatingSolver::computeTruth(const Query &query, bool &isValid) {
  bool answer;

  if (!solver->impl->computeTruth(query, isValid))
    return false;
  if (!oracle->impl->computeTruth(query, answer))
    return false;

  if (isValid != answer)
    assert(0 && "invalid solver result (computeTruth)");

  return true;
}

bool ValidatingSolver::computeValidity(const Query &query,
                                       Solver::Validity &result) {
  Solver::Validity answer;

  if (!solver->impl->computeValidity(query, result))
    return false;
  if (!oracle->impl->computeValidity(query, answer))
    return false;

  if (result != answer)
    assert(0 && "invalid solver result (computeValidity)");

  return true;
}

bool ValidatingSolver::computeValue(const Query &query, ref<Expr> &result) {
  bool answer;

  if (!solver->impl->computeValue(query, result))
    return false;
  // We don't want to compare, but just make sure this is a legal
  // solution.
  if (!oracle->impl->computeTruth(
          query.withExpr(NeExpr::create(query.expr, result)), answer))
    return false;

  if (answer)
    assert(0 && "invalid solver result (computeValue)");

  return true;
}

bool ValidatingSolver::computeInitialValues(const Query &query,
                            const std::vector<const Array *> &arr_objects,
                            std::vector<std::vector<unsigned char> > &arr_values,
                            const std::vector<const BitVecExpr *> &bv_objects,
                            std::vector<bitvec_ce_t> &bv_values,
                            const std::vector<const IntExpr *> &int_objects,
                            std::vector<int_ce_t> &int_values,  
                            bool &hasSolution) {
  bool answer;

  if (!solver->impl->computeInitialValues(query, arr_objects, arr_values,
                                          bv_objects, bv_values,
                                          int_objects, int_values, hasSolution))
    return false;

  if (hasSolution) {
    // Assert the bindings as constraints, and verify that the
    // conjunction of the actual constraints is satisfiable.
    ConstraintSet bindings;
    for (unsigned i = 0; i != arr_values.size(); ++i) {
      const Array *array = arr_objects[i];
      assert(array);
      for (unsigned j = 0; j < array->size; j++) {
        unsigned char value = arr_values[i][j];
        bindings.push_back(EqExpr::create(
            ReadExpr::create(UpdateList(array, 0),
                             ConstantExpr::alloc(j, array->getDomain())),
            ConstantExpr::alloc(value, array->getRange())));
      }
    }
    assert(0 && "SyT does not support FastCexSolver");
    // for (unsigned i = 0; i != bv_values.size(); ++i) {
    //   const Expr *bv = bv_objects[i];
    //   assert(bv);
    //   unsigned int value = bv_values[i];
    //   bindings.push_back(EqExpr::create(ref<Expr>(bv),
    //       ConstantExpr::alloc(value, bv->getWidth())));
    // }
    // ConstraintManager tmp(bindings);
    // ref<Expr> constraints = Expr::createIsZero(query.expr);
    // for (auto const &constraint : query.constraints)
    //   constraints = AndExpr::create(constraints, constraint);

    // if (!oracle->impl->computeTruth(Query(bindings, constraints), answer))
    //   return false;
    // if (!answer)
    //   assert(0 && "invalid solver result (computeInitialValues)");
  } else {
    if (!oracle->impl->computeTruth(query, answer))
      return false;
    if (!answer)
      assert(0 && "invalid solver result (computeInitialValues)");
  }

  return true;
}

SolverImpl::SolverRunStatus ValidatingSolver::getOperationStatusCode() {
  return solver->impl->getOperationStatusCode();
}

char *ValidatingSolver::getConstraintLog(const Query &query) {
  return solver->impl->getConstraintLog(query);
}

void ValidatingSolver::setCoreSolverTimeout(time::Span timeout) {
  solver->impl->setCoreSolverTimeout(timeout);
}

Solver *createValidatingSolver(Solver *s, Solver *oracle) {
  assert(0 && "SyT does not support FastCexSolver");
  return new Solver(new ValidatingSolver(s, oracle));
}
}
