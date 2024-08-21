//===-- TimingSolver.cpp --------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "TimingSolver.h"

#include "ExecutionState.h"

#include "klee/Config/Version.h"
#include "klee/Statistics/Statistics.h"
#include "klee/Statistics/TimerStatIncrementer.h"
#include "klee/Solver/Solver.h"

#include "CoreStats.h"

using namespace klee;
using namespace llvm;

/***/

bool TimingSolver::evaluate(const ConstraintSet &constraints, ref<Expr> expr,
                            Solver::Validity &result,
                            SolverQueryMetaData &metaData) {
  // Fast path, to avoid timer and OS overhead.
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(expr)) {
    result = CE->isTrue() ? Solver::True : Solver::False;
    return true;
  }

  TimerStatIncrementer timer(stats::solverTime);

  if (simplifyExprs)
    expr = ConstraintManager::simplifyExpr(constraints, expr);

  // TPOT simplifies reads
  // expr = ConstraintManager::simplifyAddresses(constraints, expr);
  // expr = ConstraintManager::simplifyReads(solver.get(), constraints, expr);
  expr = ConstraintManager::instantiteBV2IntAxioms(solver.get(), constraints, expr);

  bool success = solver->evaluate(Query(constraints, expr), result);

  metaData.queryCost += timer.delta();

  return success;
}

bool TimingSolver::mustBeTrue(const ConstraintSet &constraints, ref<Expr> expr,
                              bool &result, SolverQueryMetaData &metaData) {
  // Fast path, to avoid timer and OS overhead.
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(expr)) {
    result = CE->isTrue() ? true : false;
    return true;
  }

  TimerStatIncrementer timer(stats::solverTime);

  if (simplifyExprs)
    expr = ConstraintManager::simplifyExpr(constraints, expr);

  // TPOT simplifies reads
  // expr = ConstraintManager::simplifyAddresses(constraints, expr);
  // expr = ConstraintManager::simplifyReads(solver.get(), constraints, expr);
  expr = ConstraintManager::instantiteBV2IntAxioms(solver.get(), constraints, expr);

  bool success = solver->mustBeTrue(Query(constraints, expr), result);

  metaData.queryCost += timer.delta();

  return success;
}

bool TimingSolver::mustBeFalse(const ConstraintSet &constraints, ref<Expr> expr,
                               bool &result, SolverQueryMetaData &metaData) {
  return mustBeTrue(constraints, Expr::createIsZero(expr), result, metaData);
}

bool TimingSolver::mayBeTrue(const ConstraintSet &constraints, ref<Expr> expr,
                             bool &result, SolverQueryMetaData &metaData) {
  bool res;
  if (!mustBeFalse(constraints, expr, res, metaData))
    return false;
  result = !res;
  return true;
}

bool TimingSolver::mayBeFalse(const ConstraintSet &constraints, ref<Expr> expr,
                              bool &result, SolverQueryMetaData &metaData) {
  bool res;
  if (!mustBeTrue(constraints, expr, res, metaData))
    return false;
  result = !res;
  return true;
}

bool TimingSolver::getValue(const ConstraintSet &constraints, ref<Expr> expr,
                            ref<ConstantExpr> &result,
                            SolverQueryMetaData &metaData) {
  // Fast path, to avoid timer and OS overhead.
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(expr)) {
    result = CE;
    return true;
  }
  
  TimerStatIncrementer timer(stats::solverTime);

  if (simplifyExprs)
    expr = ConstraintManager::simplifyExpr(constraints, expr);
  // TPOT simplifies reads
  // expr = ConstraintManager::simplifyAddresses(constraints, expr);
  // expr = ConstraintManager::simplifyReads(solver.get(), constraints, expr);
  expr = ConstraintManager::instantiteBV2IntAxioms(solver.get(), constraints, expr);

  bool success = solver->getValue(Query(constraints, expr), result);

  metaData.queryCost += timer.delta();

  return success;
}

bool TimingSolver::getInitialValues(const ConstraintSet &constraints,
                        const std::vector<const Array *> &arr_objects,
                        std::vector<std::vector<unsigned char> > &arr_values,
                        const std::vector<const BitVecExpr *> &bv_objects,
                        std::vector<bitvec_ce_t> &bv_values,
                        const std::vector<const IntExpr *> &int_objects,
                        std::vector<int_ce_t> &int_values,
                        SolverQueryMetaData &metaData) {
  if (arr_objects.empty() && bv_objects.empty())
    return true;

  TimerStatIncrementer timer(stats::solverTime);

  bool success = solver->getInitialValues(
      Query(constraints, ConstantExpr::alloc(0, Expr::Bool)), arr_objects, arr_values,
                                          bv_objects, bv_values, int_objects, int_values);

  metaData.queryCost += timer.delta();

  return success;
}

std::pair<ref<Expr>, ref<Expr>>
TimingSolver::getRange(const ConstraintSet &constraints, ref<Expr> expr,
                       SolverQueryMetaData &metaData) {
  TimerStatIncrementer timer(stats::solverTime);
  auto result = solver->getRange(Query(constraints, expr));
  metaData.queryCost += timer.delta();
  return result;
}

bool TimingSolver::getCounterExample(const ConstraintSet &constraints, ref<Expr> expr,
                                    const std::vector<const Array *> &arr_objects,
                                    std::vector<std::vector<unsigned char>> &arr_values,
                                    std::vector<bool> &arr_values_ok,
                                    const std::vector<const BitVecExpr *> &bv_objects,
                                    std::vector<bitvec_ce_t> &bv_values,
                                    std::vector<bool> &bv_values_ok,
                                    const std::vector<const IntExpr *> &int_objects,
                                    std::vector<int_ce_t> &int_values,
                                    std::vector<bool> &int_values_ok,
                                    SolverQueryMetaData &metaData) {
  TimerStatIncrementer timer(stats::solverTime);

  if (simplifyExprs)
    expr = ConstraintManager::simplifyExpr(constraints, expr);

  // TPOT simplifies reads
  expr = ConstraintManager::simplifyAddresses(constraints, expr);
  expr = ConstraintManager::simplifyReads(solver.get(), constraints, expr);
  expr = ConstraintManager::instantiteBV2IntAxioms(solver.get(), constraints, expr);

  bool success = solver->getCounterExample(Query(constraints, expr), arr_objects,
                          arr_values, arr_values_ok, bv_objects, bv_values, bv_values_ok,
                          int_objects, int_values, int_values_ok);

  metaData.queryCost += timer.delta();

  return success;
}