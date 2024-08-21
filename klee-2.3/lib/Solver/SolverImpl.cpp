//===-- SolverImpl.cpp ----------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Solver/Solver.h"
#include "klee/Solver/SolverImpl.h"

using namespace klee;

SolverImpl::~SolverImpl() {}

bool SolverImpl::computeValidity(const Query &query, Solver::Validity &result) {
  bool isTrue, isFalse;
  if (!computeTruth(query, isTrue))
    return false;
  if (isTrue) {
    result = Solver::True;
  } else {
    if (!computeTruth(query.negateExpr(), isFalse))
      return false;
    result = isFalse ? Solver::False : Solver::Unknown;
  }
  return true;
}

const char *SolverImpl::getOperationStatusString(SolverRunStatus statusCode) {
  switch (statusCode) {
  case SOLVER_RUN_STATUS_SUCCESS_SOLVABLE:
    return "OPERATION SUCCESSFUL, QUERY IS SOLVABLE";
  case SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE:
    return "OPERATION SUCCESSFUL, QUERY IS UNSOLVABLE";
  case SOLVER_RUN_STATUS_FAILURE:
    return "OPERATION FAILED";
  case SOLVER_RUN_STATUS_TIMEOUT:
    return "SOLVER TIMEOUT";
  case SOLVER_RUN_STATUS_FORK_FAILED:
    return "FORK FAILED";
  case SOLVER_RUN_STATUS_INTERRUPTED:
    return "SOLVER PROCESS INTERRUPTED";
  case SOLVER_RUN_STATUS_UNEXPECTED_EXIT_CODE:
    return "UNEXPECTED SOLVER PROCESS EXIT CODE";
  case SOLVER_RUN_STATUS_WAITPID_FAILED:
    return "WAITPID FAILED FOR SOLVER PROCESS";
  default:
    return "UNRECOGNIZED OPERATION STATUS";
  }
}

bool SolverImpl::computeCounterExample(
    const Query &query, const std::vector<const Array *> &arr_objects,
    std::vector<std::vector<unsigned char>> &arr_values,
    std::vector<bool> &arr_values_ok,
    const std::vector<const BitVecExpr *> &bv_objects,
    std::vector<bitvec_ce_t> &bv_values, std::vector<bool> &bv_values_ok,
    const std::vector<const IntExpr *> &int_objects,
    std::vector<int_ce_t> &int_values, std::vector<bool> &int_values_ok,
    bool &hasSolution) {
  arr_values_ok.assign(arr_objects.size(), true);
  bv_values_ok.assign(bv_objects.size(), true);
  int_values_ok.assign(int_objects.size(), true);

  return computeInitialValues(query.withFalse(), arr_objects, arr_values,
                              bv_objects, bv_values, int_objects, int_values, hasSolution);
}
