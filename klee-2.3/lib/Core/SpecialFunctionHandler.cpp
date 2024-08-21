//===-- SpecialFunctionHandler.cpp ----------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "SpecialFunctionHandler.h"

#include "ExecutionState.h"
#include "Executor.h"
#include "Memory.h"
#include "MemoryManager.h"
#include "MergeHandler.h"
#include "Searcher.h"
#include "StatsTracker.h"
#include "TimingSolver.h"

#include "klee/Config/config.h"
#include "klee/Module/KInstruction.h"
#include "klee/Module/KModule.h"
#include "klee/Solver/SolverCmdLine.h"
#include "klee/Support/Casting.h"
#include "klee/Support/Debug.h"
#include "klee/Support/ErrorHandling.h"
#include "klee/Support/OptionCategories.h"

#include "llvm/ADT/Twine.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/Casting.h"

#include <errno.h>
#include <sstream>

using namespace llvm;
using namespace klee;

namespace {
cl::opt<bool>
    ReadablePosix("readable-posix-inputs", cl::init(false),
                  cl::desc("Prefer creation of POSIX inputs (command-line "
                           "arguments, files, etc.) with human readable bytes. "
                           "Note: option is expensive when creating lots of "
                           "tests (default=false)"),
                  cl::cat(TestGenCat));

cl::opt<bool>
    SilentKleeAssume("silent-klee-assume", cl::init(false),
                     cl::desc("Silently terminate paths with an infeasible "
                              "condition given to klee_assume() rather than "
                              "emitting an error (default=false)"),
                     cl::cat(TerminationCat));
} // namespace

/// \todo Almost all of the demands in this file should be replaced
/// with terminateState calls.

///

// FIXME: We are more or less committed to requiring an intrinsic
// library these days. We can move some of this stuff there,
// especially things like realloc which have complicated semantics
// w.r.t. forking. Among other things this makes delayed query
// dispatch easier to implement.
static SpecialFunctionHandler::HandlerInfo handlerInfo[] = {
#define add(name, handler, ret) { name, \
                                  &SpecialFunctionHandler::handler, \
                                  false, ret, false }
#define addDNR(name, handler) { name, \
                                &SpecialFunctionHandler::handler, \
                                true, false, false }
  addDNR("__assert_rtn", handleAssertFail),
  addDNR("__assert_fail", handleAssertFail),
  addDNR("__assert", handleAssertFail),
  addDNR("_assert", handleAssert),
  addDNR("abort", handleAbort),
  addDNR("_exit", handleExit),
  { "exit", &SpecialFunctionHandler::handleExit, true, false, true },
  addDNR("klee_abort", handleAbort),
  addDNR("klee_silent_exit", handleSilentExit),
  addDNR("klee_report_error", handleReportError),
  add("calloc", handleCalloc, true),
  add("free", handleFree, false),
  add("klee_assume", handleAssume, false),
  add("klee_check_memory_access", handleCheckMemoryAccess, false),
  add("klee_get_valuef", handleGetValue, true),
  add("klee_get_valued", handleGetValue, true),
  add("klee_get_valuel", handleGetValue, true),
  add("klee_get_valuell", handleGetValue, true),
  add("klee_get_value_i32", handleGetValue, true),
  add("klee_get_value_i64", handleGetValue, true),
  add("klee_define_fixed_object", handleDefineFixedObject, false),
  add("klee_get_obj_size", handleGetObjSize, true),
  add("klee_get_errno", handleGetErrno, true),
#ifndef __APPLE__
  add("__errno_location", handleErrnoLocation, true),
#else
  add("__error", handleErrnoLocation, true),
#endif
  add("klee_is_symbolic", handleIsSymbolic, true),
  add("klee_make_symbolic", handleMakeSymbolic, false),
  add("klee_mark_global", handleMarkGlobal, false),
  add("klee_open_merge", handleOpenMerge, false),
  add("klee_close_merge", handleCloseMerge, false),
  add("klee_prefer_cex", handlePreferCex, false),
  add("klee_posix_prefer_cex", handlePosixPreferCex, false),
  add("klee_print_expr", handlePrintExpr, false),
  add("klee_print_range", handlePrintRange, false),
  add("klee_set_forking", handleSetForking, false),
  add("klee_stack_trace", handleStackTrace, false),
  add("klee_warning", handleWarning, false),
  add("klee_warning_once", handleWarningOnce, false),
  add("malloc", handleMalloc, true),
  add("memalign", handleMemalign, true),
  add("realloc", handleRealloc, true),

#ifdef SUPPORT_KLEE_EH_CXX
  add("_klee_eh_Unwind_RaiseException_impl", handleEhUnwindRaiseExceptionImpl, false),
  add("klee_eh_typeid_for", handleEhTypeid, true),
#endif

  // operator delete[](void*)
  add("_ZdaPv", handleDeleteArray, false),
  // operator delete(void*)
  add("_ZdlPv", handleDelete, false),

  // operator new[](unsigned int)
  add("_Znaj", handleNewArray, true),
  // operator new(unsigned int)
  add("_Znwj", handleNew, true),

  // FIXME-64: This is wrong for 64-bit long...

  // operator new[](unsigned long)
  add("_Znam", handleNewArray, true),
  // operator new(unsigned long)
  add("_Znwm", handleNew, true),

  // Run clang with -fsanitize=signed-integer-overflow and/or
  // -fsanitize=unsigned-integer-overflow
  add("__ubsan_handle_add_overflow", handleAddOverflow, false),
  add("__ubsan_handle_sub_overflow", handleSubOverflow, false),
  add("__ubsan_handle_mul_overflow", handleMulOverflow, false),
  add("__ubsan_handle_divrem_overflow", handleDivRemOverflow, false),

  /* TPot functions */
  add("__tpot_fresh_bv", handleTpotFreshBV, true),
  add("__tpot_points_to", handleTpotPointsTo, true),
  add("__tpot_names_obj_forall", handleTpotNamesObjForall, true),
  add("__tpot_names_obj_forall_cond", handleTpotNamesObjForallCond, true),
  add("__tpot_inv", handleTpotInv, false),
  add("__tpot_forall_elem", handleTpotForallElem, true),
  add("__tpot_assert", handleTpotAssert, false),
  add("__tpot_switch_old", handleTpotSwitchOld, false),
  add("__tpot_switch_new", handleTpotSwitchNew, false),
  add("__tpot_uninterpreted", handleTpotUninterpreted, false),
  add("__tpot_assert_unchanged_except", handleTpotAssertUnchangedExcept, false),
  add("__tpot_malloc", handleTpotMalloc, true),
  add("__tpot_free", handleTpotFree, false),
  add("memset", handleMemset, true),
  add("memcpy", handleMemcpy, true),

  /* TPoT debugging functions*/
  add("__tpot_skip_invariant_check", handleSkipInvariantCheck, false),
  add("__tpot_debug_print", handleDebugPrint, false),

#undef addDNR
#undef add
};

SpecialFunctionHandler::const_iterator SpecialFunctionHandler::begin() {
  return SpecialFunctionHandler::const_iterator(handlerInfo);
}

SpecialFunctionHandler::const_iterator SpecialFunctionHandler::end() {
  // NULL pointer is sentinel
  return SpecialFunctionHandler::const_iterator(0);
}

SpecialFunctionHandler::const_iterator& SpecialFunctionHandler::const_iterator::operator++() {
  ++index;
  if ( index >= SpecialFunctionHandler::size())
  {
    // Out of range, return .end()
    base=0; // Sentinel
    index=0;
  }

  return *this;
}

int SpecialFunctionHandler::size() {
	return sizeof(handlerInfo)/sizeof(handlerInfo[0]);
}

SpecialFunctionHandler::SpecialFunctionHandler(Executor &_executor) 
  : executor(_executor) {}

void SpecialFunctionHandler::prepare(
    std::vector<const char *> &preservedFunctions) {
  unsigned N = size();

  for (unsigned i=0; i<N; ++i) {
    HandlerInfo &hi = handlerInfo[i];
    Function *f = executor.kmodule->module->getFunction(hi.name);

    // No need to create if the function doesn't exist, since it cannot
    // be called in that case.
    if (f && (!hi.doNotOverride || f->isDeclaration())) {
      preservedFunctions.push_back(hi.name);
      // Make sure NoReturn attribute is set, for optimization and
      // coverage counting.
      if (hi.doesNotReturn)
        f->addFnAttr(Attribute::NoReturn);

      // Change to a declaration since we handle internally (simplifies
      // module and allows deleting dead code).
      if (!f->isDeclaration())
        f->deleteBody();
    }
  }
}

void SpecialFunctionHandler::bind() {
  unsigned N = sizeof(handlerInfo)/sizeof(handlerInfo[0]);

  for (unsigned i=0; i<N; ++i) {
    HandlerInfo &hi = handlerInfo[i];
    Function *f = executor.kmodule->module->getFunction(hi.name);
    
    if (f && (!hi.doNotOverride || f->isDeclaration()))
      handlers[f] = std::make_pair(hi.handler, hi.hasReturnValue);
  }
}


bool SpecialFunctionHandler::handle(ExecutionState &state, 
                                    Function *f,
                                    KInstruction *target,
                                    std::vector< ref<Expr> > &arguments) {
  handlers_ty::iterator it = handlers.find(f);
  if (it != handlers.end()) {    
    Handler h = it->second.first;
    bool hasReturnValue = it->second.second;
     // FIXME: Check this... add test?
    if (!hasReturnValue && !target->inst->use_empty()) {
      executor.terminateStateOnExecError(state, 
                                         "expected return value from void special function");
    } else {
      (this->*h)(state, target, arguments);
    }
    return true;
  } else {
    // see if f is an uninterpreted function
    for (auto &uf : uninterpFunctions) {
      if (f == uf) {
        this->handleUninterpFunc(state, target, arguments, f);
        return true;
      }
    }
    return false;
  }
}

/****/

// reads a concrete string from memory
std::string 
SpecialFunctionHandler::readStringAtAddress(ExecutionState &state, 
                                            ref<Expr> addressExpr) {
  ObjectPair op;
  addressExpr = executor.toUnique(state, addressExpr);
  if (!isa<ConstantExpr>(addressExpr)) {
    executor.terminateStateOnUserError(
        state, "Symbolic string pointer passed to one of the klee_ functions");
    return "";
  }
  ref<ConstantExpr> address = cast<ConstantExpr>(addressExpr);
  if (!state.addressSpace.resolveOne(address, op)) {
    executor.terminateStateOnUserError(
        state, "Invalid string pointer passed to one of the klee_ functions");
    return "";
  }
  const MemoryObject *mo = op.first;
  const ObjectState *os = op.second;

  auto relativeOffset = mo->getOffsetExpr(address);
  // the relativeOffset must be concrete as the address is concrete
  size_t offset = cast<ConstantExpr>(relativeOffset)->getZExtValue();

  std::ostringstream buf;
  char c = 0;
  for (size_t i = offset; i < mo->size; ++i) {
    ref<Expr> cur = os->read8(i, false);
    cur = executor.toUnique(state, cur);
    assert(isa<ConstantExpr>(cur) && 
           "hit symbolic char while reading concrete string");
    c = cast<ConstantExpr>(cur)->getZExtValue(8);
    if (c == '\0') {
      // we read the whole string
      break;
    }

    buf << c;
  }

  if (c != '\0') {
      klee_warning_once(0, "String not terminated by \\0 passed to "
                           "one of the klee_ functions");
  }

  return buf.str();
}

/****/

void SpecialFunctionHandler::handleAbort(ExecutionState &state,
                                         KInstruction *target,
                                         std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 0 && "invalid number of arguments to abort");
  executor.terminateStateOnError(state, "abort failure",
                                 StateTerminationType::Abort);
}

void SpecialFunctionHandler::handleExit(ExecutionState &state,
                                        KInstruction *target,
                                        std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 1 && "invalid number of arguments to exit");
  executor.terminateStateOnExit(state, ConstantExpr::alloc(0, Expr::Bool));
}

void SpecialFunctionHandler::handleSilentExit(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 1 && "invalid number of arguments to exit");
  executor.terminateStateEarly(state, "", StateTerminationType::SilentExit);
}

void SpecialFunctionHandler::handleAssert(ExecutionState &state,
                                          KInstruction *target,
                                          std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 3 && "invalid number of arguments to _assert");
  executor.terminateStateOnError(
      state, "ASSERTION FAIL: " + readStringAtAddress(state, arguments[0]),
      StateTerminationType::Assert);
}

void SpecialFunctionHandler::handleAssertFail(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 4 &&
         "invalid number of arguments to __assert_fail");
  executor.terminateStateOnError(
      state, "ASSERTION FAIL: " + readStringAtAddress(state, arguments[0]),
      StateTerminationType::Assert);
}

void SpecialFunctionHandler::handleReportError(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 4 &&
         "invalid number of arguments to klee_report_error");

  // arguments[0,1,2,3] are file, line, message, suffix
  executor.terminateStateOnError(
      state, readStringAtAddress(state, arguments[2]),
      StateTerminationType::ReportError, "",
      readStringAtAddress(state, arguments[3]).c_str());
}

void SpecialFunctionHandler::handleOpenMerge(ExecutionState &state,
    KInstruction *target,
    std::vector<ref<Expr> > &arguments) {
  if (!UseMerge) {
    klee_warning_once(0, "klee_open_merge ignored, use '-use-merge'");
    return;
  }

  state.openMergeStack.push_back(
      ref<MergeHandler>(new MergeHandler(&executor, &state)));

  if (DebugLogMerge)
    llvm::errs() << "open merge: " << &state << "\n";
}

void SpecialFunctionHandler::handleCloseMerge(ExecutionState &state,
    KInstruction *target,
    std::vector<ref<Expr> > &arguments) {
  if (!UseMerge) {
    klee_warning_once(0, "klee_close_merge ignored, use '-use-merge'");
    return;
  }
  Instruction *i = target->inst;

  if (DebugLogMerge)
    llvm::errs() << "close merge: " << &state << " at [" << *i << "]\n";

  if (state.openMergeStack.empty()) {
    std::ostringstream warning;
    warning << &state << " ran into a close at " << i << " without a preceding open";
    klee_warning("%s", warning.str().c_str());
  } else {
    assert(executor.mergingSearcher->inCloseMerge.find(&state) ==
               executor.mergingSearcher->inCloseMerge.end() &&
           "State cannot run into close_merge while being closed");
    executor.mergingSearcher->inCloseMerge.insert(&state);
    state.openMergeStack.back()->addClosedState(&state, i);
    state.openMergeStack.pop_back();
  }
}

void SpecialFunctionHandler::handleNew(ExecutionState &state,
                         KInstruction *target,
                         std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 && "invalid number of arguments to new");

  executor.executeAlloc(state, arguments[0], false, target);
}

void SpecialFunctionHandler::handleDelete(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  // FIXME: Should check proper pairing with allocation type (malloc/free,
  // new/delete, new[]/delete[]).

  // XXX should type check args
  assert(arguments.size()==1 && "invalid number of arguments to delete");
  executor.executeFree(state, arguments[0]);
}

void SpecialFunctionHandler::handleNewArray(ExecutionState &state,
                              KInstruction *target,
                              std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 && "invalid number of arguments to new[]");
  executor.executeAlloc(state, arguments[0], false, target);
}

void SpecialFunctionHandler::handleDeleteArray(ExecutionState &state,
                                 KInstruction *target,
                                 std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 && "invalid number of arguments to delete[]");
  executor.executeFree(state, arguments[0]);
}

void SpecialFunctionHandler::handleMalloc(ExecutionState &state,
                                  KInstruction *target,
                                  std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 && "invalid number of arguments to malloc");
  executor.executeAlloc(state, arguments[0], false, target);
}

void SpecialFunctionHandler::handleMemalign(ExecutionState &state,
                                            KInstruction *target,
                                            std::vector<ref<Expr>> &arguments) {
  if (arguments.size() != 2) {
    executor.terminateStateOnUserError(state,
      "Incorrect number of arguments to memalign(size_t alignment, size_t size)");
    return;
  }

  std::pair<ref<Expr>, ref<Expr>> alignmentRangeExpr =
      executor.solver->getRange(state.constraints, arguments[0],
                                state.queryMetaData);
  ref<Expr> alignmentExpr = alignmentRangeExpr.first;
  auto alignmentConstExpr = dyn_cast<ConstantExpr>(alignmentExpr);

  if (!alignmentConstExpr) {
    executor.terminateStateOnUserError(state, "Could not determine size of symbolic alignment");
    return;
  }

  uint64_t alignment = alignmentConstExpr->getZExtValue();

  // Warn, if the expression has more than one solution
  if (alignmentRangeExpr.first != alignmentRangeExpr.second) {
    klee_warning_once(
        0, "Symbolic alignment for memalign. Choosing smallest alignment");
  }

  executor.executeAlloc(state, arguments[1], false, target, false, 0,
                        alignment);
}

#ifdef SUPPORT_KLEE_EH_CXX
void SpecialFunctionHandler::handleEhUnwindRaiseExceptionImpl(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 1 &&
         "invalid number of arguments to _klee_eh_Unwind_RaiseException_impl");

  ref<ConstantExpr> exceptionObject = dyn_cast<ConstantExpr>(arguments[0]);
  if (!exceptionObject.get()) {
    executor.terminateStateOnExecError(state, "Internal error: Symbolic exception pointer");
    return;
  }

  if (isa_and_nonnull<SearchPhaseUnwindingInformation>(
          state.unwindingInformation.get())) {
    executor.terminateStateOnExecError(
        state,
        "Internal error: Unwinding restarted during an ongoing search phase");
    return;
  }

  state.unwindingInformation =
      std::make_unique<SearchPhaseUnwindingInformation>(exceptionObject,
                                                        state.stack.size() - 1);

  executor.unwindToNextLandingpad(state);
}

void SpecialFunctionHandler::handleEhTypeid(ExecutionState &state,
                                            KInstruction *target,
                                            std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 1 &&
         "invalid number of arguments to klee_eh_typeid_for");

  executor.bindLocal(target, state, executor.getEhTypeidFor(arguments[0]));
}
#endif // SUPPORT_KLEE_EH_CXX

void SpecialFunctionHandler::handleAssume(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 && "invalid number of arguments to klee_assume");
  
  ref<Expr> e = arguments[0];
  
  if (e->getWidth() != Expr::Bool)
    e = NeExpr::create(e, ConstantExpr::create(0, e->getWidth()));
  
  bool res;
  bool success __attribute__((unused)) = executor.solver->mustBeFalse(
      state.getConstraints(true), e, res, state.queryMetaData);
  assert(success && "FIXME: Unhandled solver failure");
  if (res) {
    tpot_message("Pruning state due to assume(...)");
    executor.terminateState(state);
  } else {
    executor.addConstraintGuarded(state, e);
  }
}

void SpecialFunctionHandler::handleIsSymbolic(ExecutionState &state,
                                KInstruction *target,
                                std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 && "invalid number of arguments to klee_is_symbolic");

  executor.bindLocal(target, state, 
                     ConstantExpr::create(!isa<ConstantExpr>(arguments[0]),
                                          Expr::Int32));
}

void SpecialFunctionHandler::handlePreferCex(ExecutionState &state,
                                             KInstruction *target,
                                             std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_prefex_cex");

  ref<Expr> cond = arguments[1];
  if (cond->getWidth() != Expr::Bool)
    cond = NeExpr::create(cond, ConstantExpr::alloc(0, cond->getWidth()));

  state.addCexPreference(cond);
}

void SpecialFunctionHandler::handlePosixPreferCex(ExecutionState &state,
                                             KInstruction *target,
                                             std::vector<ref<Expr> > &arguments) {
  if (ReadablePosix)
    return handlePreferCex(state, target, arguments);
}

void SpecialFunctionHandler::handlePrintExpr(ExecutionState &state,
                                  KInstruction *target,
                                  std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_print_expr");

  std::string msg_str = readStringAtAddress(state, arguments[0]);
  llvm::errs() << msg_str << ":" << arguments[1] << "\n";
}

void SpecialFunctionHandler::handleSetForking(ExecutionState &state,
                                              KInstruction *target,
                                              std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_set_forking");
  ref<Expr> value = executor.toUnique(state, arguments[0]);
  
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(value)) {
    state.forkDisabled = CE->isZero();
  } else {
    executor.terminateStateOnUserError(state, "klee_set_forking requires a constant arg");
  }
}

void SpecialFunctionHandler::handleStackTrace(ExecutionState &state,
                                              KInstruction *target,
                                              std::vector<ref<Expr> > &arguments) {
  state.dumpStack(outs());
}

void SpecialFunctionHandler::handleWarning(ExecutionState &state,
                                           KInstruction *target,
                                           std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 && "invalid number of arguments to klee_warning");

  std::string msg_str = readStringAtAddress(state, arguments[0]);
  klee_warning("%s: %s", state.stack.back().kf->function->getName().data(), 
               msg_str.c_str());
}

void SpecialFunctionHandler::handleWarningOnce(ExecutionState &state,
                                               KInstruction *target,
                                               std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_warning_once");

  std::string msg_str = readStringAtAddress(state, arguments[0]);
  klee_warning_once(0, "%s: %s", state.stack.back().kf->function->getName().data(),
                    msg_str.c_str());
}

void SpecialFunctionHandler::handlePrintRange(ExecutionState &state,
                                  KInstruction *target,
                                  std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_print_range");

  std::string msg_str = readStringAtAddress(state, arguments[0]);
  llvm::errs() << msg_str << ":" << arguments[1];
  if (!isa<ConstantExpr>(arguments[1])) {
    // FIXME: Pull into a unique value method?
    ref<ConstantExpr> value;
    bool success __attribute__((unused)) = executor.solver->getValue(
        state.constraints, arguments[1], value, state.queryMetaData);
    assert(success && "FIXME: Unhandled solver failure");
    bool res;
    success = executor.solver->mustBeTrue(state.constraints,
                                          EqExpr::create(arguments[1], value),
                                          res, state.queryMetaData);
    assert(success && "FIXME: Unhandled solver failure");
    if (res) {
      llvm::errs() << " == " << value;
    } else { 
      llvm::errs() << " ~= " << value;
      std::pair<ref<Expr>, ref<Expr>> res = executor.solver->getRange(
          state.constraints, arguments[1], state.queryMetaData);
      llvm::errs() << " (in [" << res.first << ", " << res.second <<"])";
    }
  }
  llvm::errs() << "\n";
}

void SpecialFunctionHandler::handleGetObjSize(ExecutionState &state,
                                  KInstruction *target,
                                  std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_get_obj_size");
  Executor::ExactResolutionList rl;
  executor.resolveExact(state, arguments[0], rl, "klee_get_obj_size");
  for (Executor::ExactResolutionList::iterator it = rl.begin(), 
         ie = rl.end(); it != ie; ++it) {
    executor.bindLocal(
        target, *it->second,
        ConstantExpr::create(it->first.first->size,
                             executor.kmodule->targetData->getTypeSizeInBits(
                                 target->inst->getType())));
  }
}

void SpecialFunctionHandler::handleGetErrno(ExecutionState &state,
                                            KInstruction *target,
                                            std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==0 &&
         "invalid number of arguments to klee_get_errno");
#ifndef WINDOWS
  int *errno_addr = executor.getErrnoLocation(state);
#else
  int *errno_addr = nullptr;
#endif

  // Retrieve the memory object of the errno variable
  ObjectPair result;
  bool resolved = state.addressSpace.resolveOne(
      ConstantExpr::create((uint64_t)errno_addr, Expr::Int64), result);
  if (!resolved)
    executor.terminateStateOnUserError(state, "Could not resolve address for errno");
  executor.bindLocal(target, state, result.second->read(0, Expr::Int32, false));
}

void SpecialFunctionHandler::handleErrnoLocation(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr> > &arguments) {
  // Returns the address of the errno variable
  assert(arguments.size() == 0 &&
         "invalid number of arguments to __errno_location/__error");

#ifndef WINDOWS
  int *errno_addr = executor.getErrnoLocation(state);
#else
  int *errno_addr = nullptr;
#endif

  executor.bindLocal(
      target, state,
      ConstantExpr::create((uint64_t)errno_addr,
                           executor.kmodule->targetData->getTypeSizeInBits(
                               target->inst->getType())));
}
void SpecialFunctionHandler::handleCalloc(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==2 &&
         "invalid number of arguments to calloc");

  ref<Expr> size = MulExpr::create(arguments[0],
                                   arguments[1]);
  executor.executeAlloc(state, size, false, target, true);
}

void SpecialFunctionHandler::handleRealloc(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==2 &&
         "invalid number of arguments to realloc");
  ref<Expr> address = arguments[0];
  ref<Expr> size = arguments[1];

  Executor::StatePair zeroSize =
      executor.fork(state, Expr::createIsZero(size), true, BranchType::Realloc);

  if (zeroSize.first) { // size == 0
    executor.executeFree(*zeroSize.first, address, target);   
  }
  if (zeroSize.second) { // size != 0
    Executor::StatePair zeroPointer =
        executor.fork(*zeroSize.second, Expr::createIsZero(address), true,
                      BranchType::Realloc);

    if (zeroPointer.first) { // address == 0
      executor.executeAlloc(*zeroPointer.first, size, false, target);
    } 
    if (zeroPointer.second) { // address != 0
      Executor::ExactResolutionList rl;
      executor.resolveExact(*zeroPointer.second, address, rl, "realloc");
      
      for (Executor::ExactResolutionList::iterator it = rl.begin(), 
             ie = rl.end(); it != ie; ++it) {
        executor.executeAlloc(*it->second, size, false, target, false, 
                              it->first.second);
      }
    }
  }
}

void SpecialFunctionHandler::handleFree(ExecutionState &state,
                          KInstruction *target,
                          std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 &&
         "invalid number of arguments to free");
  executor.executeFree(state, arguments[0]);
}

void SpecialFunctionHandler::handleCheckMemoryAccess(ExecutionState &state,
                                                     KInstruction *target,
                                                     std::vector<ref<Expr> > 
                                                       &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_check_memory_access");

  ref<Expr> address = executor.toUnique(state, arguments[0]);
  ref<Expr> size = executor.toUnique(state, arguments[1]);
  if (!isa<ConstantExpr>(address) || !isa<ConstantExpr>(size)) {
    executor.terminateStateOnUserError(state, "check_memory_access requires constant args");
  } else {
    ObjectPair op;

    if (!state.addressSpace.resolveOne(cast<ConstantExpr>(address), op)) {
      executor.terminateStateOnError(state,
                                     "check_memory_access: memory error",
                                     StateTerminationType::Ptr,
                                     executor.getAddressInfo(state, address));
    } else {
      ref<Expr> chk = 
        op.first->getBoundsCheckPointer(address, 
                                        cast<ConstantExpr>(size)->getZExtValue());
      if (!chk->isTrue()) {
        executor.terminateStateOnError(state,
                                       "check_memory_access: memory error",
                                       StateTerminationType::Ptr,
                                       executor.getAddressInfo(state, address));
      }
    }
  }
}

void SpecialFunctionHandler::handleGetValue(ExecutionState &state,
                                            KInstruction *target,
                                            std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_get_value");

  executor.executeGetValue(state, arguments[0], target);
}

void SpecialFunctionHandler::handleDefineFixedObject(ExecutionState &state,
                                                     KInstruction *target,
                                                     std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_define_fixed_object");
  assert(isa<ConstantExpr>(arguments[0]) &&
         "expect constant address argument to klee_define_fixed_object");
  assert(isa<ConstantExpr>(arguments[1]) &&
         "expect constant size argument to klee_define_fixed_object");
  
  uint64_t address = cast<ConstantExpr>(arguments[0])->getZExtValue();
  uint64_t size = cast<ConstantExpr>(arguments[1])->getZExtValue();
  MemoryObject *mo = executor.memory->allocateFixed(address, size, state.prevPC->inst);
  executor.bindObjectInState(state, mo, false);
  mo->isUserSpecified = true; // XXX hack;
}

void SpecialFunctionHandler::handleMakeSymbolic(ExecutionState &state,
                                                KInstruction *target,
                                                std::vector<ref<Expr> > &arguments) {
  std::string name;

  if (arguments.size() != 3) {
    executor.terminateStateOnUserError(state,
        "Incorrect number of arguments to klee_make_symbolic(void*, size_t, char*)");
    return;
  }

  name = arguments[2]->isZero() ? "" : readStringAtAddress(state, arguments[2]);

  if (name.length() == 0) {
    name = "unnamed";
    klee_warning("klee_make_symbolic: renamed empty name to \"unnamed\"");
  }

  Executor::ExactResolutionList rl;
  executor.resolveExact(state, arguments[0], rl, "make_symbolic");
  
  for (Executor::ExactResolutionList::iterator it = rl.begin(), 
         ie = rl.end(); it != ie; ++it) {
    const MemoryObject *mo = it->first.first;
    mo->setName(name);
    
    const ObjectState *old = it->first.second;
    ExecutionState *s = it->second;
    
    if (old->readOnly) {
      executor.terminateStateOnUserError(*s, "cannot make readonly object symbolic");
      return;
    } 

    // FIXME: Type coercion should be done consistently somewhere.
    bool res;
    bool success __attribute__((unused)) = executor.solver->mustBeTrue(
        s->constraints,
        EqExpr::create(
            ZExtExpr::create(arguments[1], Context::get().getPointerWidth()),
            mo->getSizeExpr()),
        res, s->queryMetaData);
    assert(success && "FIXME: Unhandled solver failure");
    
    if (res) {
      executor.executeMakeSymbolic(*s, mo, name);
    } else {      
      executor.terminateStateOnUserError(*s, "Wrong size given to klee_make_symbolic");
    }
  }
}

void SpecialFunctionHandler::handleMarkGlobal(ExecutionState &state,
                                              KInstruction *target,
                                              std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_mark_global");  

  Executor::ExactResolutionList rl;
  executor.resolveExact(state, arguments[0], rl, "mark_global");
  
  for (Executor::ExactResolutionList::iterator it = rl.begin(), 
         ie = rl.end(); it != ie; ++it) {
    const MemoryObject *mo = it->first.first;
    assert(!mo->isLocal);
    mo->isGlobal = true;
  }
}

void SpecialFunctionHandler::handleAddOverflow(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  executor.terminateStateOnError(state, "overflow on addition",
                                 StateTerminationType::Overflow);
}

void SpecialFunctionHandler::handleSubOverflow(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  executor.terminateStateOnError(state, "overflow on subtraction",
                                 StateTerminationType::Overflow);
}

void SpecialFunctionHandler::handleMulOverflow(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  executor.terminateStateOnError(state, "overflow on multiplication",
                                 StateTerminationType::Overflow);
}

void SpecialFunctionHandler::handleDivRemOverflow(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  executor.terminateStateOnError(state, "overflow on division or remainder",
                                 StateTerminationType::Overflow);
}

// ----------------------------------------------------- //
// ---------------- forall_elem helpers ---------------- //
// ----------------------------------------------------- //

void SpecialFunctionHandler::parseForallElemArgs(
  ExecutionState &state,              /*in*/
  KInstruction *target,               /*in*/
  std::vector<ref<Expr> > &arguments, /*in*/
  ref<Expr> &arrayPtr,                /*out*/
  const MemoryObject *&obj,           /*out*/
  ForallElemProperty *&prop           /*out*/) {

  CallInst *ci = dyn_cast<CallInst>(target->inst);

  // This should never happen due to the C function signature.
  assert(arguments.size() >= 6 && "Invalid number of arguments to forall_elem");
  assert(ci && "forall_elem called with non-call instruction");

  assert(arguments[0]->getWidth() == 64 && "forall_elem: first argument does not have pointer width");
  NoOpResolutionList rl = executor.resolveAddressNoOp(state, arguments[0], NULL, NULL, 0, "");
  arrayPtr = arguments[0];
  // We don't support forall_elem properties for pointers that can resolve to multiple objects for now.
  // TODO: this is easily fixable. Simply fork before handling the forall_elem call.
  assert(rl.isSingleResolution() && "multiple resolution in forall_elem");
  obj = rl.objects[0].first;
  assert(obj && "First argument does not resolve to an object");

  // Size of the array, as reported by sizeof() in C.
  unsigned arraySizeConst = cast<ConstantExpr>(arguments[1])->getZExtValue();
  ref<Expr> arraySize = NULL;
  unsigned elemSize = cast<ConstantExpr>(arguments[2])->getZExtValue();
  ref<Expr> addrElem0 = arguments[3];
  ref<Expr> addrElem0Field = arguments[4];
  unsigned fieldOffset = cast<ConstantExpr>(SubExpr::create(addrElem0Field, addrElem0))->getZExtValue();
  if (obj->size != arraySizeConst) {
    if (obj->size == 0) {
      const SytSSMemoryObject *smo = dynamic_cast<const SytSSMemoryObject *>(obj);
      assert(smo && "Zero-size object is not a SytSSMemoryObject");
      if (ConstantExpr *sizeExpr = dyn_cast<ConstantExpr>(smo->symbolicSize)) {
        assert(sizeExpr && "Zero-size object has non-constant symbolic size");
        arraySizeConst = sizeExpr->getZExtValue();
      } else {
        arraySize = smo->symbolicSize;
      }
    } else {
      tpot_message("The object size is %d and the arraySize passed in "
                 "syt_forall_elem is %d, will use the object size.",
                 obj->size, arraySizeConst);
       arraySizeConst = obj->size;
    }
  }

  ref<Expr> numElems;
  if (arraySize.isNull()) {
    assert(arraySizeConst % elemSize == 0);
    numElems = ConstantExpr::create(arraySizeConst / elemSize, 64);
  } else {
    // a bug caused by this would be hard to catch. Let's check to be safe..
    ref<Expr> modZero = EqExpr::create(URemExpr::create(arraySize, ConstantExpr::create(elemSize, 64)), ConstantExpr::create(0, 64));
    bool res;
    bool success __attribute__((unused)) = executor.solver->mustBeTrue(
        state.getConstraints(/*useHeapConstraints=*/true), modZero, res, state.queryMetaData);
    assert(success && "FIXME: Unhandled solver failure");
    assert(res && "Array size is not a multiple of element size");
    numElems = UDivExpr::create(arraySize, ConstantExpr::create(elemSize, 64));
  }

  llvm::Function *condFunc = executor.getTargetFunction(ci->getOperand(5), state);
  assert(condFunc && "Fourth argument is not a function pointer");

  ref<Expr> arrayOffset = obj->getOffsetExpr(arguments[0]);
  if (arrayOffset->getWidth() != 0) {
    arrayOffset = executor.convertToInteger(state, arrayOffset);
  }
  if (obj->address == 0 && !obj->uniqueHeapAddress.isNull()) {
    arrayOffset = SubExpr::create(arrayOffset, obj->uniqueHeapAddress);
  }
  // arrayOffset = executor.toUnique(state, arrayOffset);

  // Check specifically for offset 0. Counterexamples involving bv2int are temporarily broken.
  // So we can not use toConstant(). Need to fix this soon, but let's ignore for now.
  ref<Expr> offset_zero = EqExpr::create(ConstantExpr::create(0, 64), arrayOffset);
  bool res;
  bool solver_success __attribute__((unused)) = executor.solver->mustBeTrue(
      state.getConstraints(/*useHeapConstraints=*/true), offset_zero, res, state.queryMetaData);
  assert(solver_success && "FIXME: Unhandled solver failure");
  if (res) {
    arrayOffset = ConstantExpr::create(0, 64);
  }

  // We compute this twice... see below and refactor.
  const FunctionType *fType = dyn_cast<FunctionType>(
        cast<PointerType>(condFunc->getType())->getElementType());
  auto ty =  cast<PointerType>(fType->getParamType(0))->getElementType();
  auto width = executor.getWidthForLLVMType(ty);
  unsigned fieldSize = width / 8;

  std::vector<ref<Expr>> extraArgs;
  assert(arguments.size() - 6 == fType->getNumParams() - 2 && "Invalid number of arguments to forall_elem");
  for (unsigned i = 6; i < arguments.size(); i++) {
    assert(arguments[i]->getWidth() == executor.getWidthForLLVMType(fType->getParamType(i - 4)));
    extraArgs.push_back(arguments[i]);
  }

  prop = new ForallElemProperty(arrayOffset, numElems, elemSize, condFunc, extraArgs);
}

// Check if the current context is strong enough to prove that the forall_elem property holds.
bool SpecialFunctionHandler::checkForallElem(
  ExecutionState &state,
  ref<Expr> arrayPtr,
  const MemoryObject *obj,
  ForallElemProperty *prop,
  int forallElemCtr  /* to give fresh symbols unique names */) {

  ExecutionState *tmpState = state.branch();
  executor.processTree->attach(state.ptreeNode, tmpState, &state, BranchType::SytComputeLambda);
  ref<Expr> elemIdx = BitVecExpr::create("forall_elem_test_idx_" + std::to_string(forallElemCtr++), 64);
  ref<Expr> elemPtr = AddExpr::create(arrayPtr, 
      MulExpr::create(elemIdx, ConstantExpr::create(prop->elemSize, 64)));

  // Add the constraint that the index is within bounds.
  executor.addConstraintGuarded(*tmpState, 
    AndExpr::create(
      UleExpr::create(ConstantExpr::create(0, 64), elemIdx),
      UltExpr::create(elemIdx, 
        prop->numElems->getWidth() == 64 ? prop->numElems : BV2IntExpr::getBVForm(prop->numElems))));

  std::vector<ExecutionState*> branches = {tmpState};
  if (!obj->forallElem.empty()) {
    ref<Expr> address = AddExpr::create(arrayPtr, MulExpr::create(elemIdx, ConstantExpr::create(prop->elemSize, 64)));
    ref<Expr> elemOffset;
    if (obj->address == 0 && !obj->uniqueHeapAddress.isNull()) {
      // this is a heap object
      // TODO: implement the stack/heap differentation more elegantly.
      assert(prop->arrayOffset->getWidth() == 0 || dyn_cast<ConstantExpr>(prop->arrayOffset));
      elemOffset = AddExpr::create(
          prop->arrayOffset,
          executor.convertToInteger(state, 
            MulExpr::create(
                elemIdx, ConstantExpr::create(prop->elemSize, 64))));
      address = executor.convertToInteger(state, address);
    } else {
      // this is a stack/global object
      elemOffset = 
        AddExpr::create(
          prop->arrayOffset,
          MulExpr::create(
              elemIdx, ConstantExpr::create(prop->elemSize, 64)));
    }

    // TODO: this "save added states" thing is an ad-hoc solution we use in multpile places. Implement a better solution.
    auto tmp_addedStates = executor.addedStates; 
    executor.addedStates.clear();
    executor.instantiateForallElem(*tmpState, obj, elemOffset, address);
    branches = executor.addedStates;
    branches.push_back(tmpState);
    executor.addedStates = tmp_addedStates;
    if (obj->address == 0 && !obj->uniqueHeapAddress.isNull()) {
      // this is a heap object
      // We also need to instantiate a bv2int axiom for all stores indices into the array in order to avoid incompleteness.
      // (elemIdx == storeIdx && bv2int(elemIdx) == bv2int(storeIdx)) ||
      //    (elemIdx != storeIdx && bv2int(elemIdx) != bv2int(storeIdx))

      // -- get object state --
      // We don't know where this object is (heap, as, a havoced layer..)
      // We should implement something tidier here.
      // For now we have a dirty implementation with checks on it.
      const ObjectState *os = tmpState->heap.findObject(obj);
      if (os) {
        // the orignial state must have the object in the heap, too.
        assert(state.heap.findObject(obj));
      } else {
        // look at havoced heaps.
        for (int i = 0; i < tmpState->activeInvariants.size(); i++) {
          os = tmpState->activeInvariants[i].heap->findObject(obj);
          if (os) {
            assert(state.activeInvariants[i].heap->findObject(obj));
            break;
          }
        }
      }
      assert(os && "Object not found in heap. Are you sure this is not a stack/global object?");

      ref<UpdateNode> curUpdate = os->updates.head;
      while (curUpdate) {
        ref<Expr> storeIdx = curUpdate->index;
        assert(storeIdx->getWidth() == 0);
        ref<Expr> rawStoreIdx=BV2IntExpr::getBVForm(storeIdx);
        ref<Expr> arrStoreIdxBV=UDivExpr::create(
            SubExpr::create(rawStoreIdx, 
              prop->arrayOffset->getWidth() == 0 ? BV2IntExpr::getBVForm(prop->arrayOffset) : prop->arrayOffset),
            ConstantExpr::create(prop->elemSize, 64));

        ref<Expr> elemIdxInt = executor.convertToInteger(state, elemIdx);
        ref<Expr> arrStoreIdxInt =  executor.convertToInteger(state, arrStoreIdxBV);
        ref<Expr> axiomInst = OrExpr::create(
          AndExpr::create(
            EqExpr::create(elemIdx, arrStoreIdxBV),
            EqExpr::create(elemIdxInt, arrStoreIdxInt)),
          AndExpr::create(
            NeExpr::create(elemIdx, arrStoreIdxBV),
            NeExpr::create(elemIdxInt, arrStoreIdxInt)));
        executor.addConstraintGuarded(*tmpState, axiomInst);
        curUpdate = curUpdate->next;
      }
    } 
  }

  // we check if the lambda holds for an arbitary index over all branches.
  // a more precise approach would be to return true over the branches where this holds,
  // but for now we only for temporarily and only return true over the original state if it holds
  // over all branches.
  assert(branches.size() > 0);
  bool success = true;
  int i = 1;
  std::vector<ref<Expr>> args;
  for (auto s : branches) {
    // compute the lambda for the arbitrary index.
    args.clear();
    args.push_back(elemPtr);
    args.push_back(elemIdx);
    args.insert(args.end(), prop->extraArgs.begin(), prop->extraArgs.end());
    tpot_message("Checking forall_elem property. State (%d/%d). Fork reason: %s", 
      i, branches.size(),
      s->forkReason.c_str());
    bool res = executor.lambdaMustReturnTrue(*s, prop->condFunc, args);
    if (!res) {
      success = false;
      break;
    }
    i++;
  }
  
  for (auto s : branches) {
    delete s;
  }
  return success;
}

// Memoize the property with dummy arguments, so that it can be instantiated with
// actual arguments later.
// TODO: we shouldn't need to call computeLambda twice for checkForallElem and memoizeForallElem.
bool SpecialFunctionHandler::memoizeForallElem(
  ExecutionState &state,
  ref<Expr> arrayPtr,
  const MemoryObject *obj,
  ForallElemProperty *prop,
  int forallElemCtr  /* to give fresh symbols unique names */) {

  // compute the lambda over the initial state so it gets memoized.
  //? Careful: are we sure we aren't memoizing the lambda with constraints on its arguments?
  //? Here, yes, since the arguments are fresh. But what about the other call sites? 
  // dummyArgIdx is args[1]: the index for which the condition is to be evaluated.
  ref<Expr> dummyArgIdx = BitVecExpr::create("dummy_arg_idx", 64);
  // This is the address of the element at dummyArgIdx.
  ref<Expr> dummyElemPtr = AddExpr::create(arrayPtr, MulExpr::create(dummyArgIdx, ConstantExpr::create(prop->elemSize, 64)));

  std::vector<ref<Expr>> args;
  args.push_back(dummyElemPtr);
  args.push_back(dummyArgIdx);
  args.insert(args.end(), prop->extraArgs.begin(), prop->extraArgs.end());

  MemoryObject *dummyMo = NULL;

  // TODO: this is [dummy object logic]. Fix later.
  // const FunctionType *fType = dyn_cast<FunctionType>(
  //     cast<PointerType>(condFunc->getType())->getElementType());
  // if (fieldSize == 8 && isa<PointerType>(fType->getParamType(0))) {
  //   ref<Expr> dummy_obj_addr = executor.convertToInteger(state, args[0]);

  //   // copied from below.. refactor.
  //   ref<Expr> elemOffset = 
  //     AddExpr::create(arrayOffset,
  //       executor.convertToInteger(state, 
  //           AddExpr::create(ConstantExpr::create(fieldOffset, 64),
  //             MulExpr::create(args[1], ConstantExpr::create(elemSize, 64)))));

  //   // elemOffset = executor.convertToInteger(state, elemOffset);
  //   Expr::Width type = fieldSize * 8;


  //   // const ObjectState *os = state.heap.findObject(obj);
  //   // We don't know where this object is (heap, as, a havoced layer..)
  //   // We should implement something tidier here.
  //   // For now we have a dirty implementation.
  //   const ObjectState *os = state.heap.findObject(obj);
  //   if (!os) {
  //     for (int i = 0; i < state.activeInvariants.size(); i++) {
  //       os = state.activeInvariants[i].heap->findObject(obj);
  //       if (os) {
  //         // assert(state.activeInvariants[i].heap->findObject(obj));
  //         break;
  //       }
  //     }
  //   }

  //   ref<Expr> readValue = os->read(elemOffset, type, false);

  //   // TODO: have computeLambda create this dummy object, so that it does not exist
  //   // outside of the forked state.
  //   executor.addConstraintGuarded(state, EqExpr::create(args[0], readValue));

  //   auto ty =  cast<PointerType>(fType->getParamType(0))->getElementType();
  //   auto width = executor.getWidthForLLVMType(ty);
  //   ref<Expr> size = ConstantExpr::create(width / 8 , 64);
  //   size = executor.convertToInteger(state, size);

  //   assert(width % 8 == 0 && "syt_names_obj_forall_cond with non-byte-sized elements");
  //   SytSSMemoryObject *mo = new SytSSMemoryObject(/*address=*/0, size, /*isLocal=*/false,
  //                                     /*isGlobal=*/true, false, /*allocSite=*/NULL,
  //                                     NULL, /*uniqueHeapAddress=*/dummy_obj_addr);
  //   auto name = "dummy_object_forallelem_" + std::to_string(forallElemCtr++);
  //   mo->setName(name);
  //   dummyMo = mo;
  // }

  executor.computeLambda(state, prop->condFunc, args,
    /*non_null_constr=*/NULL, dummyMo, /*mustReturnTrue=*/NULL, LambdaPurpose::MEMOIZE); 
}


void SpecialFunctionHandler::handleTpotForallElem(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  static int forallElemCtr = 1; // to give fresh symbols unique names

  ref<Expr> arrayPtr;               // pointer to the array
  const MemoryObject *obj;          // the memory object that contains the array
  ForallElemProperty *prop;         // the property struct that aggregates parameters

  // A version of the forall_elem implementation allowed forallElem properties to
  // refer to fZone instances. We simplified the implementation by only allowing a
  // single such instance to be referred to and supplied a dummy object to memoize
  // the forallElem lambdas. This code is now commented out and tagged with [dummy object logic]. 

  parseForallElemArgs(state, target, arguments, arrayPtr, obj, prop);


  // let's not waste time in checkForallElem if we are assuming invariants.
  if (state.syt_stage != ASSUME_INVARIANTS && state.syt_stage != COMPUTE_LOOP_INV) {
    if (checkForallElem(state, arrayPtr, obj, prop, forallElemCtr)) {
      // return true
      executor.bindLocal(target, state, ConstantExpr::create(1, Expr::Bool));
      return;
    }
    if (state.syt_stage == ASSERT_INVARIANTS) {
      // Don't waste time memoizing if we are in the assert invariants stage.
      // return false
      executor.bindLocal(target, state, ConstantExpr::create(0, Expr::Bool));
      return;
    }
  }

  memoizeForallElem(state, arrayPtr, obj, prop, forallElemCtr);
  // Add a new forallElemProperty.
  prop->placeholderCond = EqExpr::create(
    BitVecExpr::create("forall_elem_placeholder_" + std::to_string(forallElemCtr++), 2), 
    ConstantExpr::create(1, 2));

  obj->forallElem.push_back(prop);

  // return placoholder
  executor.bindLocal(target, state, prop->placeholderCond);
}

// Klee's assert forks the state. We want to simply fail instead.
void SpecialFunctionHandler::handleTpotAssert(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  assert(arguments.size() == 1);
  ref<Expr> cond = arguments[0];
  assert(cond->getWidth() == 1);

  bool res;
  bool success __attribute__((unused)) = executor.solver->mustBeTrue(
      state.constraints, cond, res, state.queryMetaData);
  assert(success && "FIXME: Unhandled solver failure");
  if (!res) {
    executor.getCounterExample(state, executor.solver, state.constraints, cond, state.queryMetaData);
    executor.getFailingCodePath(state);
    executor.terminateStateOnError(
      state, "ASSERT FAIL: " + target->inst->getParent()->getParent()->getName().str() + " " + target->inst->getParent()->getName().str() + " " + target->inst->getName().str(),
      StateTerminationType::Assert);
  }
}


/*
 * Creates a fresh bitvector. 
 * Currently only used to create bound variables for quantified expressions.
 */
void SpecialFunctionHandler::handleTpotFreshBV(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  static int index = 1; // to give fresh symbols unique names

  assert(arguments.size()==3 && "invalid number of arguments to syt_fresh_bv");                    
  std::string name = readStringAtAddress(state, arguments[0]);

  auto constWidthExpr = dyn_cast<ConstantExpr>(arguments[1]);
  assert(constWidthExpr && "syt_declare_uniqptr with symbolic size");
  uint64_t width = constWidthExpr->getZExtValue(64);

  if (width != Expr::Int32 && width != Expr::Int64 &&
      width != Expr::Bool && width != Expr::Int8 &&
      width != Expr::Int16 && width != Expr::Fl80) {
    klee_warning("Unsupported bitvector width in syt_fresh_bv");
  }

  CallInst *ci = dyn_cast<CallInst>(target->inst); 
  assert(ci && "syt_forall_elem called with non-call instruction");

  
  ref<BitVecExpr> e = BitVecExpr::create("syt_fresh_bv__" + name + "." + std::to_string(index++), width);

  state.addSymbolic(e);

  // return the fresh value
  executor.bindLocal(target, state, e);
}

ref<Expr> SpecialFunctionHandler::allocateFreshPtr(ExecutionState &state, std::string name) {
  unsigned id = 0;
  std::string uniqueName = name;
  while (!state.arrayNames.insert(uniqueName).second) {
    uniqueName = name + "_" + llvm::utostr(++id);
  }

  // Experimental: use integers
  return IntExpr::create(uniqueName);
}

ref<Expr> SpecialFunctionHandler::allocateFreshBV64(ExecutionState &state, std::string name) {
  unsigned id = 0;
  std::string uniqueName = name;
  while (!state.arrayNames.insert(uniqueName).second) {
    uniqueName = name + "_" + llvm::utostr(++id);
  }

  return BitVecExpr::create(uniqueName, 64);
}

SytSSMemoryObject *SpecialFunctionHandler::allocateInHeap(ExecutionState &state, MemoryObject *mo, 
  ref<Expr> obj_addr, ref<Expr> size,
  std::string obj_name, bool constrainSize, bool skipParents) {
  if (mo) {
    // tpot_message("allocateInHeap called with mo!=NULL. Are you sure you know what you're doing?");
  }
  ref<Expr> size_int = size->getWidth() == 0 ? size : executor.convertToInteger(state, size);
  
  // create the object unless it's already created and passed as an argument (e.g. dummy objects)
  SytSSMemoryObject *newObj = NULL;
  if (mo == NULL) {
    ref<Expr> basePtrBvForm = allocateFreshBV64(state, "base__" + obj_name);
    ref<Expr> basePtr = executor.convertToInteger(state, basePtrBvForm);
    
    newObj = new SytSSMemoryObject(/*address=*/0, size_int, /*isLocal=*/false,
                                    /*isGlobal=*/true, false, /*allocSite=*/NULL,
                                    NULL, /*uniqueHeapAddress=*/basePtr);
    newObj->setName(obj_name);
    mo = newObj;
  } else {
    // assert(mo->uniqueHeapAddress == obj_addr);
    SytSSMemoryObject *smo = dynamic_cast<SytSSMemoryObject *>(mo);
    if (smo) {
      assert(*smo->symbolicSize == *size_int);
    } else {
      assert(*mo->getSizeExpr() == *BV2IntExpr::getBVForm(size_int));
    }
  }

  for (int idx = state.heap.heapObjects.size(); idx >= 0; --idx) {
    if (allocateInHeap(state, mo, obj_addr, size, obj_name, constrainSize, skipParents, idx)) {
      return newObj;
    }
  }

  executor.terminateStateOnUserError(
            state, "no suitable heap location found for allocation");
  if (newObj)
    delete newObj;
  return NULL;
}

// helper for allocateInHeap
ref<Expr> SpecialFunctionHandler::getAllocCond(ExecutionState &state, ref<Expr> basePtr,
                                             ref<Expr> size, bool constrainSize, int idx) {
  // For now this funciton is generic to integers and bitvectors (for basePtr, size), as we are experimenting.
  // We should make it specific to one kind.

  ref<Expr> basePtr_int = basePtr->getWidth() == 0 ? basePtr : executor.convertToInteger(state, basePtr);
  ref<Expr> size_int = size->getWidth() == 0 ? size : executor.convertToInteger(state, size);

  // the is_unique smt function encodes how many bytes of unique memory is pointed to by the given pointer.
  std::vector<ref<Expr>> args;
  args.push_back(basePtr_int);
  ref<Expr> uniq_sz = FuncAppExpr::create("is_unique", args);

  // Record a "hint" -- We will later turn this into eager allocation
  executor.uniqPtrHints.push_back(std::make_pair(basePtr, size));

  // Does size fit in the unique memory?
  ref<Expr> allocCond = EqExpr::create(size_int, uniq_sz);

  // -- To rule out any corner cases resulting from overflows,
  // we require pointers to be positive. This can be fixed later.
  allocCond = AndExpr::create(allocCond,
    SltExpr::create(ConstantExpr::create(0, 64), basePtr));

  assert(idx >= 0 && idx <= state.heap.heapObjects.size());
  ref<Expr> cond_heap_order = ConstantExpr::create(1, 1);
  if (idx > 0) {
    auto prev_obj = state.heap.heapObjects[idx-1].first;
    const SytSSMemoryObject *prev_smo = dynamic_cast<const SytSSMemoryObject *>(prev_obj);
    ref<Expr> prev_sz = prev_smo ? prev_smo->symbolicSize : (ref<Expr>) prev_obj->getSizeExpr();
    ref<Expr> prev_end = AddExpr::create(prev_obj->uniqueHeapAddress, prev_sz);

    if (basePtr->getWidth() != 0) {
      prev_end = BV2IntExpr::getBVForm(prev_end);
    }

    cond_heap_order = AndExpr::create(
      cond_heap_order,
      UleExpr::create(prev_end, basePtr));
  }
  if (idx < state.heap.heapObjects.size()) {
    ref<Expr> obj_end = AddExpr::create(basePtr, size);
    ref<Expr> next_begin = state.heap.heapObjects[idx].first->uniqueHeapAddress;

    if (basePtr->getWidth() != 0) {
      next_begin = BV2IntExpr::getBVForm(next_begin);
    }

    cond_heap_order = AndExpr::create(
      cond_heap_order,
      UleExpr::create(obj_end, next_begin));
  }

  allocCond = AndExpr::create(allocCond, cond_heap_order);

  if (constrainSize) {
    ref<Expr> sz_positive = SltExpr::create(ConstantExpr::create(0, 64), size);
    allocCond = AndExpr::create(allocCond, sz_positive);
  }
  return allocCond;
}

// allocates the object at index idx and returns true if allowed by the constraints.
// otherwise, returns false.
bool SpecialFunctionHandler::allocateInHeap(ExecutionState &state, MemoryObject *mo, 
  ref<Expr> obj_addr, ref<Expr> size,
  std::string obj_name, bool constrainSize, bool skipParents, int idx) {

  assert(obj_addr->getWidth() == 0 && "heap pointer is not integer");
  if (size->getWidth() != 0) {
    // let's worry about heap objects with symbolic sizes later.
    // Combining integers with constant expressions is ok.
    // Binary operators check for this before throwing a type mismatch.
    ConstantExpr *CE = dyn_cast<ConstantExpr>(size);
    assert(CE && "need to convert between symbolic bitvec and symbolic int");
  }

  assert(!mo->uniqueHeapAddress.isNull() && mo->address == 0 && "invalid memory object for heap allocation");
  ref<Expr> basePtr = mo->uniqueHeapAddress;

  // Unfortunately we need the bv version of allocCond, too.
  // ref<Expr> allocCond = getAllocCond(state, basePtr, size, constrainSize, idx);
  ref<Expr> allocCond = getAllocCond(state, BV2IntExpr::getBVForm(basePtr), 
                                    size->getWidth() == 0 ? BV2IntExpr::getBVForm(size) : size,  // size might be a constant bv
                                    constrainSize, idx);

  // ref<Expr> allocAndEq = AndExpr::create(allocCond, EqExpr::create(obj_addr, basePtr));
  
  // Looks like we need the BV constraints. Constrain the bv form (until we find a more permanent solution). 
  // This will add constraints over integers too (through addConstraint)
  if (!obj_addr->bvForm) {
    obj_addr->bvForm = BV2IntExpr::getBVForm(obj_addr);
  }
  if (!basePtr->bvForm) {
    basePtr->bvForm = BV2IntExpr::getBVForm(basePtr);
  }
  ref<Expr> eqCond = EqExpr::create(obj_addr->bvForm, basePtr->bvForm);
  ref<Expr> allocAndEq = AndExpr::alloc(allocCond, eqCond);

  // We reserve the object across all states. This could be made much more elegant
  // and efficient.
  bool success, res;

  // save lambdaPC before allocating on the current state
  ref<Expr> lambdaPC = state.lambdaParent ? executor.getLambdaPathCondition(state) : NULL;

  // Allocate the object on the current state
  auto s = &state;
  // we do not want the allocCond added to the lambda path constraint, since the allocation
  // condition will be propagated to the parent by other means.
  // TODO: do this for the addConstarintGuarded calls below, too.
  bool saveLambdaPath = !(s->lambdaPathConstraints.empty());
  std::vector<ref<Expr>> curLambdaPath;
  if (saveLambdaPath) 
    curLambdaPath =  s->lambdaPathConstraints.back();
  bool addSuccess = executor.addConstraintGuarded(*s, allocCond, /*failureIsFatal=*/false);
  if (!addSuccess) {
    return false;
  }
  if (saveLambdaPath)
    s->lambdaPathConstraints.back() = curLambdaPath;

  executor.addConstraintGuarded(*s, eqCond);
  executor.updateAddressSimplTable(*s, obj_addr, basePtr);

  s->heap.heap_end = AddExpr::create(basePtr, size);
  state.heap.namesToObjects[obj_name] = std::make_pair(basePtr, size);;
  executor.executeMakeSymbolic(*s, mo, mo->name); // binds mo in s

  //! Allocate the object on all states generated in all lambda siblings
  if (state.lambdaParent) {

    for (auto s: executor.addedStates) {
      // the current state is already handled
      if(s == &state) continue;
      // when handling an fzone resolution, addedStates may contain states
      // forked during the current instruction. Allocating the new object in those would
      // make the state inconsistent.
      if(s->prevPC == state.prevPC) continue;

      ref<Expr> condEq = Expr::createImplies(lambdaPC, 
                          EqExpr::create(obj_addr->bvForm, basePtr->bvForm));
      ref<Expr> allocAndConditionalEq = AndExpr::create(allocCond, condEq);

      addSuccess = executor.addConstraintGuarded(*s, allocAndConditionalEq, /*failureIsFatal=*/false);
      if (!addSuccess) {
        // this should not happen anymore now that the equality is conditional.
        assert(false && "allocation failed on sibling state");

        // // if it is impossible for the sibling to host the object, we simply skip the allocation.
        // // this is fine since the sibling will never create a copy of the object on its own.

        // // still, let's print a warning.
        // klee_warning("skipping allocation of %s on sibling state at %d", obj_name.c_str(), s->prevPC->info->assemblyLine);
      }

      s->heap.heap_end = AddExpr::create(basePtr, size);
      state.heap.namesToObjects[obj_name] = std::make_pair(basePtr, size);;
      executor.executeMakeSymbolic(*s, mo, mo->name); // binds mo in s
    }

    if (!skipParents) {
      // ! Allocate the object on all lambda ancestors
      ExecutionState *cur = state.lambdaParent;
      while (cur != NULL) {
        // Allocate the object conditionally.

        // similarly to above, we add use the bvForm since we might rely on bv constraints.
        ref<Expr> condEq = Expr::createImplies(lambdaPC, 
                          EqExpr::create(obj_addr->bvForm, basePtr->bvForm));
        ref<Expr> allocAndConditionalEq = AndExpr::create(allocCond, condEq);

        executor.addConstraintGuarded(*cur, allocAndConditionalEq);
        cur->heap.heap_end = AddExpr::create(basePtr, size);
        state.heap.namesToObjects[obj_name] = std::make_pair(basePtr, size);;
        executor.executeMakeSymbolic(*cur, mo, mo->name); // binds mo in s

        if (cur->lambdaParent != NULL)
          lambdaPC = AndExpr::create(lambdaPC, executor.getLambdaPathCondition(*cur));

        cur = cur->lambdaParent;
      }
    }
  }

  // TODO: consider parents' siblings...
  // allocate on lambdaParentAddedStates?
  return true;
}

void SpecialFunctionHandler::__handleTpotPointsTo(ExecutionState &state,
                            KInstruction *target,
                            ref<Expr> ptr,
                            std::string obj_name,
                            ref<Expr> size) {

  // Check that the size can't be negative
  ref<Expr> size_positive = SltExpr::create(ConstantExpr::create(0, 64), size);
  bool res;
  bool success __attribute__((unused)) = executor.solver->mustBeTrue(
      state.getConstraints(/*useHeapConstraints=*/true), size_positive, res, state.queryMetaData);
  assert(success && "FIXME: Unhandled solver failure");
  if (!res) {
    executor.terminateStateOnUserError(
        state, "invalid points_to call (size can be <= 0)");
  }
  
  if (ptr->getWidth() != 0) {
    ptr = executor.convertToInteger(state, ptr);
  }
  if (size->getWidth() != 0) {
    size = executor.convertToInteger(state, size);
  }
    
  ref<Expr> obj_addr;
  
  // This was an old optimization. Commented out for now.
  // Does there already exist an object with the same name?
  // auto &addr_map = state.heap.namesToObjects;
  // auto it = addr_map.find(obj_name);
  // if ( it != addr_map.end())
  //   obj_addr = it->second.first;  // TODO: check that the size matches
  if(false) {} // dummy if to avoid compilation error

  else if (!state.heap.hasUnnamed()){
    //  --- create (reserve) a fresh object ---
    ref<Expr> obj_addr_bvForm = allocateFreshBV64(state, std::string("addr__") + obj_name);
    obj_addr = executor.convertToInteger(state, obj_addr_bvForm);

    // Allocate the object.
    MemoryObject *mo;
    // The size is symbolic. Create a symbolic-sized memory object
    mo = new SytSSMemoryObject(/*address=*/0, size, /*isLocal=*/false,
                                    /*isGlobal=*/true, false, /*allocSite=*/NULL,
                                    NULL, /*uniqueHeapAddress=*/obj_addr);

    auto name = "obj_at__" + obj_name;
    mo->setName(name);
    allocateInHeap(state, mo, obj_addr, size, obj_name, false);

    // ! shortcut to support the invariant skipping optimization.
    // ! We should remove this and resolve global pointers, forking accordingly, when invariant skipping is enabled.
    if (state.invBeingAssumed != NULL) {
      // update invariant namings (in the lambda root)
      auto s = &state;
      while (s->lambdaParent) {
        s = s->lambdaParent;
      }
      assert(s->invBeingAssumed == state.invBeingAssumed);
      s->invNamings[state.invBeingAssumed].push_back(std::make_pair(mo, name));
    }

  } else {
    // --- name the memory object this pointer points to --- //

    // if there are cases where it points to already named objects, or it points to nothing
    // return false on those cases. Otherwise return true.

    // We need to fix the implementation here.
    // Using executeMemoryOperation directly might not be the best idea.
    unsigned obj_size = 1;
    executor.executeMemoryOperation(state, Executor::memop_type::MEMOP_NAME, 
        ptr, NULL, target, obj_size, obj_name);
    return;
  }

  // return ptr == obj_addr.
  ref<Expr> ret = EqExpr::create(ptr->bvForm, obj_addr->bvForm);
  executor.bindLocal(target, state, ret);
}

void SpecialFunctionHandler::handleTpotPointsTo(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==3 && "invalid number of arguments to syt_points_to");      

  ref<Expr> ptr = arguments[0];
  std::string obj_name = readStringAtAddress(state, arguments[1]);
  ref<Expr> size = arguments[2];
  assert(size->getWidth() == Expr::Int64 && "wrong size width in syt_points_to");
  __handleTpotPointsTo(state, target, ptr, obj_name, size);
}

void SpecialFunctionHandler::_handleTpotNamesObjForall(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments,
                            NoOpResolutionList *rl_out,
                            ExecutionState *&tmpState_out,
                            ref<Expr> &ptr_out) {
  static int forall_zone_index = 1;
  static int test_index = 1;

  assert(arguments.size() == 3 && "Invalid number of arguments to syt_name_obj_forall");
  CallInst *ci = dyn_cast<CallInst>(target->inst);
  assert(ci && "syt_names_obj_forall called with non-call instruction");
  llvm::Function *f_ptr = executor.getTargetFunction(ci->getOperand(0), state);
  assert(f_ptr && "The first argument to syt_names_obj_forall is not a function pointer");
  llvm::Function *f_sz = executor.getTargetFunction(ci->getOperand(1), state);
  assert(f_sz && "The second argument to syt_names_obj_forall is not a function pointer");

  ref<Expr> bound_var = BitVecExpr::create("i_test" + std::to_string(test_index++) , 64);
  std::vector< ref<Expr> > lambda_arguments;
  lambda_arguments.push_back(bound_var);

  ref<Expr> non_null_constr;
  ref<Expr> ptr = executor.computeLambda(state, f_ptr, lambda_arguments, &non_null_constr);
  ref<Expr> obj_size = executor.computeLambda(state, f_sz, lambda_arguments);
  std::string obj_name = readStringAtAddress(state, arguments[2]);

  auto fzone_name = "fzone_at__" + obj_name;

  // --- Check if namesObjForall is already known  ---
  // let's not waste time with this unless we are asserting invariants.
  if (state.syt_stage == ASSERT_INVARIANTS) {
    ExecutionState *tmpState = state.branch();
    executor.processTree->attach(state.ptreeNode, tmpState, &state, BranchType::SytComputeLambda);

    // Pick an i that names an object, (i.e. does not make ptr NULL)
    // if ptr is NULL for all i, the property holds trivially.
    bool addSuccess = executor.addConstraintGuarded(*tmpState,
      NotExpr::create(EqExpr::create(ptr, ConstantExpr::create(0, 64))),
      /*failureIsFatal=*/false);
    if (addSuccess) {
      // Resolve ptr
      NoOpResolutionList rl = executor.resolveAddressNoOp(*tmpState, ptr, NULL, NULL, 0, "");

      //! When we unroll short loops, we can acutally exaust all possibilities for the fzone.
      // assert(rl.fzone.first && "this is probably a bug");


      if (rl.fzone.first && rl.fzone.first->name != fzone_name) {
        goto check_fail;
        // TODO: account for renaming here. Make the naming mechanism for fzones
        // similar to that of memory objects. (i.e. names reset between checks).
      }

      for (auto it : rl.objects) {
        const MemoryObject *mo = it.first;
        // careful: name the objects in the original state, not tmpState.
        const ObjectState *os = state.heap.findObject(mo);
        bool name_success = state.heap.getWriteable(mo, os)->name(fzone_name + "_inst");
        if (!name_success) {
          goto check_fail;
        }
      }
      if (rl_out) *rl_out = rl;
    }
    

  
    // the property is already known
    executor.bindLocal(target, state, ConstantExpr::create(1, Expr::Bool));
    tmpState_out = tmpState;
    ptr_out = ptr;
    return;
  }
check_fail:

  // create the forall zone
  ForallZone *fzone = new ForallZone(obj_size, bound_var, ptr, f_ptr, f_sz, fzone_name);

  // add the fzone to the current state                              
  state.heap.fzones.push_back(fzone);

  // add to lambda siblings?
  // TODO

  // add it to all lambda parents
  ExecutionState *curS = state.lambdaParent ;
  while (curS != NULL) {
    curS->heap.fzones.push_back(fzone);
    curS = curS->lambdaParent;
  }

  // Make the function return Forall(i, ptr != null ==> ptr is in forall zone).
  
  ref<Expr> ptr_int = executor.convertToInteger(state, ptr);
  ref<Expr> obj_sz_int = executor.convertToInteger(state, obj_size);

  ref<Expr> allocated = 
    EqExpr::create(
      FuncAppExpr::create("is_unique", std::vector<ref<Expr>>{ptr_int}),
      obj_sz_int);

  ref<Expr> ptr_null =
    EqExpr::create(ptr, ConstantExpr::create(0, 64));

  // forall i. ("return values that are not constant are not null") and (ptr != null ==> (ptr in bounds))

  //? Do we need the non-null constraints? Perhaps it makes sense to include it iff there are no reads in ptr..
  //? i.e. when the namesobjforall acutally represents an array.
  ref<Expr> ret = ForallExpr::create(bound_var, 
    // AndExpr::create(non_null_constr,
      OrExpr::create(ptr_null, allocated)
      //)
  );

  // use the integer version of the constraint
  std::vector<ref<Expr>> unsignedExprs;
  ret =  BV2IntExpr::convertConstraint(ret, unsignedExprs);
  ref<Expr> unsignedConstrs = state.getUnsignedConstraints(unsignedExprs);
  //? Why And them here rather than adding them to the state through regular means?
  ret = AndExpr::create(ret, unsignedConstrs);
  
  // Make sure the fzone constraint is satisfiable.
  bool res;
  bool success __attribute__((unused)) = executor.solver->mustBeFalse(
      state.getConstraints(/*useHeapConstraints=*/true), ret, res, state.queryMetaData);
  assert(success && "FIXME: Unhandled solver failure");
  assert(!res && "Fzone constraint is unsatisfiable");

  // Make sure that the forall constraint is only used when needed.
  // Not sure how to create a Bool in z3.. We do it the hacky way for now.
  // we allocate 2-bit vectors, since Klee optimizes away the equality with 1-bit vectors.
  ref<Expr> ret_placeholder = EqExpr::create(BitVecExpr::create("NOF_PH_" + obj_name + "("+
    std::to_string(forall_zone_index++)+")",
    
    2), ConstantExpr::create(1, 2));
  ref<Expr> placeholder_constraint = EqExpr::create(ret_placeholder, ret);
  placeholder_constraint->exprClass = Expr::FZoneOnly;

  if (fzone) {
    fzone->fZoneConstraint = placeholder_constraint;
  }

  // add the placeholder to lambda parent states as well
  ExecutionState *cur = &state;
  while (cur != NULL) {
    executor.addConstraint(*cur, placeholder_constraint);
    cur = cur->lambdaParent;
  }

  executor.bindLocal(target, state, ret_placeholder);
}

void SpecialFunctionHandler::handleTpotNamesObjForall(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  ExecutionState *unusedTmpState = NULL;
  ref<Expr> unusedPtr = NULL;
  _handleTpotNamesObjForall(state, target, arguments, NULL, unusedTmpState, unusedPtr);
}

void SpecialFunctionHandler::handleTpotNamesObjForallCond(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  static int index = 0; // to give fresh symbols unique names

  CallInst *ci = dyn_cast<CallInst>(target->inst);
  llvm::Function *f = executor.getTargetFunction(ci->getOperand(3), state);
  assert(f && "Fourth argument is not a function pointer");

  arguments.pop_back(); // remove the function pointer

  NoOpResolutionList rl;
  // we need the same assumptions over i that the original namesObjForall had.
  // So, we use the tmpState it created.
  ExecutionState *tmpState;
  ref<Expr> ptr;
  _handleTpotNamesObjForall(state, target, arguments, &rl, tmpState, ptr);
  // --- Check if namesObjForallCond is already known  ---
  // let's not waste time with this unless we are asserting invariants.
  if (state.syt_stage == ASSERT_INVARIANTS) {
    if (rl.empty()) {
      // there is no choice of i that does not produce a null pointer
      // the property trivially holds.
      executor.bindLocal(target, state, ConstantExpr::create(1, Expr::Bool));
      return;
    }


    assert(rl.fzone.first); // this is probably a bug

    
    // This might be redundant, but let's actually do the resolution and instantiate
    // the property over resulting states before computing lMRT.

    // Passing target here is inconsequential. It will later be overwritten.
    // It is, however, convenient since the read is byte-sized.
    auto tmp_addedStates = executor.addedStates; 
    executor.addedStates.clear();
    executor.executeMemoryOperation(*tmpState, Executor::memop_type::MEMOP_READ, ptr, 0, target, 0, "");
    std::vector<ExecutionState*> branches = executor.addedStates;
    branches.push_back(tmpState);
    executor.addedStates = tmp_addedStates;

    bool success = true;
    int i = 1;
    for (auto s : branches) {
      std::vector<ref<Expr>> args; 
      args.push_back(ptr);

      // We might want to move this to lamdaMustReturnTrue.
      // We don't want the objects lMRT creates to be added to the _state_'s parent.
      s->lambdaParent = NULL;

      tpot_message("Checking fzone property. State (%d/%d). Fork reason: %s", 
        i, branches.size(),
        s->forkReason.c_str());

      bool res = executor.lambdaMustReturnTrue(*s, f, args);

      if (!res) {
        success = false;
        break;
      }
      i++;
    }

    if (success) {
      executor.bindLocal(target, state, ConstantExpr::create(1, Expr::Bool));
      return;
    }
    assert(0);
  }

  // find the freshly created forall zone
  std::string obj_name = readStringAtAddress(state, arguments[2]);
  const ForallZone *fzone = state.heap.fzones.back();
  assert(fzone && fzone->name == "fzone_at__" + obj_name 
      && "syt_names_obj_forall_cond did not create a forall zone");

  ref<Expr> cond = EqExpr::create(BitVecExpr::create("forall_zone_prop_active_" + std::to_string(++index), 2), 
                                  ConstantExpr::create(1, 2));

  ref<Expr> dummy_arg_bv = BitVecExpr::create("dummy_arg" + std::to_string(index), 64);
  ref<Expr> dummy_arg = executor.convertToInteger(state, dummy_arg_bv);
  std::vector<ref<Expr>> args;
  args.push_back(dummy_arg_bv);

  // the lambda expects a pointer resolving to the forall zone.
  // Let's create a dummy object for dummy_arg to resolve to.
  // TODO: do this in a similar fashion to forallElem. Create a temporary state.
  const FunctionType *fType = 
        dyn_cast<FunctionType>(cast<PointerType>(f->getType())->getElementType());
  auto ty =  cast<PointerType>(fType->getParamType(0))->getElementType();
  auto width = executor.getWidthForLLVMType(ty);
  ref<Expr> size = ConstantExpr::create(width / 8 , 64); 
  assert(width % 8 == 0 && "syt_names_obj_forall_cond with non-byte-sized elements");
  SytSSMemoryObject *mo = new SytSSMemoryObject(/*address=*/0, 
                                      executor.convertToInteger(state, size),
                                       /*isLocal=*/false,
                                    /*isGlobal=*/true, false, /*allocSite=*/NULL,
                                    NULL, /*uniqueHeapAddress=*/dummy_arg);
  mo->setName("dummy_object_" + std::to_string(index));
  allocateInHeap(state, mo, dummy_arg, size, obj_name);

  executor.computeLambda(state, f, args, NULL, mo, NULL, LambdaPurpose::MEMOIZE);

  ForallZoneProperty *prop = new ForallZoneProperty(cond, f);
  fzone->fzoneProperty = prop;

  // the handleTpotNamesObjForall(...) call has already written a return value. We add a conjunction.
  ref<Expr> conjunction = AndExpr::create(
    cond,
    executor.getDestCell(state, target).value);
  
  executor.bindLocal(target, state, conjunction);
}


void SpecialFunctionHandler::handleTpotInv(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  static int layer_idx = 0; // to give fresh symbols unique names

  CallInst *ci = dyn_cast<CallInst>(target->inst);
  llvm::Function *f = executor.getTargetFunction(ci->getOperand(0), state);
  auto fType = dyn_cast<FunctionType>(cast<PointerType>(f->getType())->getElementType());
  unsigned firstModifiedFieldIdx = 1 + fType->getNumParams();

  std::vector<ref<Expr> > lambda_arguments;
  for (unsigned i = 1; i < firstModifiedFieldIdx; i++) {
    assert(fType->getParamType(i-1)->isPointerTy() 
      && "invariant function with non-pointer argument");
    lambda_arguments.push_back(arguments[i]);
  }
  ref<Expr> invPreHavoc = executor.computeLambda(state, f, lambda_arguments);

  // Check whether the invariant holds
  bool holds;
  bool success __attribute__((unused)) = executor.solver->mustBeTrue(
      state.getConstraints(/*useHeapConstraints=*/true), invPreHavoc, holds, state.queryMetaData);
  assert(success && "FIXME: Unhandled solver failure");

  // Check if this invariant is active
  for (int i = state.activeInvariants.size() - 1; i >= 0; i--) {
    if (state.activeInvariants[i].ki == target) {
      if(state.activeInvariants[i].nonHavocedModified) {
        // It means this branch modified non-havoced memory.
        // It should not have looped back.
        executor.terminateStateOnUserError(
            state, "modified unhavoced memory and looped back to invariant");
      }

      if (!holds) {
        executor.terminateStateOnUserError(
            state, "invariant is not maintained");
      }
      tpot_message("invariant is maintained (%d)", state.curLine());
      executor.interpreterHandler->incPathsCompleted();
      executor.terminateState(state);
      return;
    }
  }
  if (!holds) {
    executor.terminateStateOnUserError(
        state, "invariant does not hold initially");
  }
  tpot_message("invariant holds initially");

  // parse the modified variables
  std::vector<ref<Expr>> modified_addr;
  std::vector<ref<Expr>> modified_size;
  unsigned num_modified = 0;
  
  if (arguments.size() > firstModifiedFieldIdx) {
    assert((arguments.size() - firstModifiedFieldIdx) % 2 == 0 && "invalid number of arguments to syt_inv");
    num_modified = (arguments.size() - firstModifiedFieldIdx) / 2;
    // can't use reserve here.. these refs get dec'd.
    // modified_addr.reserve(arguments.size() - 1);
    // modified_size.reserve(arguments.size() - 1);
    for (unsigned i = 0; i < num_modified; i++) {
      assert(arguments[firstModifiedFieldIdx + 2*i]->getWidth() == Expr::Int64 
        && "syt_inv with non-pointer argument");
      modified_addr.push_back(arguments[firstModifiedFieldIdx + 2*i]);
    }
    for (unsigned i = 0; i < num_modified; i++) {
      assert(arguments[firstModifiedFieldIdx + 2*i + 1]->getWidth() == Expr::Int64 
        && "unexpected size argument to syt_inv");
      modified_size.push_back(arguments[firstModifiedFieldIdx + 2*i + 1]);
    }
  }

  // Then, switch to an address space where only the modified variables are available.
  // all writes must resolve within this address space.
  // -- construct the address space -- //
  // for now that's a heap.
  Heap *havoced_heap = new Heap();
  AddressSpace *havoced_addressSpace = new AddressSpace();
  layer_idx++;
  for (unsigned i = 0; i < num_modified; ++i) {
    int fZoneIdx;
    //! how about we just do a memory resolution here, and havoc per-object instead of per-byte?
    //! The downside would be that we expose objects at tpot's interface.
    ref<Expr> addrInt = executor.convertToInteger(state, modified_addr[i]);
    ref<Expr> sizeInt = executor.convertToInteger(state, modified_size[i]);
    if (executor.checkHeapSafety(state, modified_addr[i], sizeInt, /*useFZoneConstraints=*/false, fZoneIdx)) {


      const SytSSMemoryObject *mo = new SytSSMemoryObject(/*address=*/0, sizeInt, /*isLocal=*/false,
                                        /*isGlobal=*/true, false, /*allocSite=*/NULL,
                                        NULL, /*uniqueHeapAddress=*/addrInt);
      auto name = "havoced_obj_" + std::to_string(i) + "_layer_" + std::to_string(layer_idx);

      // TODO: find a way to just use allocateInHeap here... 
      /*
          Ideally, the constarints between heap addresses would already be present in the state..
      */

      // copied from executeMakeSymbolic...
      unsigned id = 0;
      std::string uniqueName = name;
      while (!state.arrayNames.insert(uniqueName).second) {
        uniqueName = name + "_" + llvm::utostr(++id);
      }
      mo->setName(uniqueName);
      Expr::Width domain = Expr::Int32;
      if (mo->address == 0 && !mo->uniqueHeapAddress.isNull()) {
        // this is a heap object. It should be indexed by Z3 integers.
        domain = 0;
      }

      unsigned int array_size = mo->size;
      
      const SytSSMemoryObject *smo = dynamic_cast<const SytSSMemoryObject *>(mo);
      if (smo) {
        if (ConstantExpr *CE = dyn_cast<ConstantExpr>(smo->symbolicSize)) {
          array_size = CE->getZExtValue();
        }
      }

      const Array *array = executor.arrayCache.CreateArray(uniqueName, array_size,
        0, 0, domain);
      ObjectState *os = new SytSSObjectState(mo, array);
      havoced_heap->bindObject(mo, os);
      state.addSymbolic(mo, array);


    } else {
      ConstantExpr *CE = dyn_cast<ConstantExpr>(modified_addr[i]);
      if (!CE) {
        executor.terminateStateOnUserError(state, "tpot_inv currently does not support symbolic addresses that are not heap-safe");
      }
      uint64_t conc_addr = CE->getZExtValue();
      CE = dyn_cast<ConstantExpr>(modified_size[i]);
      if (!CE) {
        executor.terminateStateOnUserError(state, "tpot_inv currently does not support symbolic sizes for objects that are not heap-safe");
      }
      uint64_t conc_sz = CE->getZExtValue();
      const MemoryObject *mo = new MemoryObject(/*address=*/conc_addr, conc_sz, /*isLocal=*/false,
                                        /*isGlobal=*/true, false, /*allocSite=*/NULL,
                                        NULL, /*uniqueHeapAddress=*/NULL);
      auto name = "havoced_obj_" + std::to_string(i) + "_layer_" + std::to_string(layer_idx);
      unsigned id = 0;
      std::string uniqueName = name;
      while (!state.arrayNames.insert(uniqueName).second) {
        uniqueName = name + "_" + llvm::utostr(++id);
      }
      mo->setName(uniqueName);
      const Array *array = executor.arrayCache.CreateArray(uniqueName, mo->size);
      ObjectState *os = new ObjectState(mo, array);
      havoced_addressSpace->bindObject(mo, os);
      state.addSymbolic(mo, array);
    }
    
  }

  // Make the invariant active
  state.activeInvariants.push_back(
      InvHavocLevel {
        .ki = target,
        .heap = havoced_heap,
        .addressSpace = havoced_addressSpace,
        .nonHavocedModified = false
      }
  );

  // compute the lambda in COMPUTE_LOOP_INV mode
  // (this will for instance keep forallElem from trying to prove that the property is already known).
  auto tmp = state.syt_stage;
  state.syt_stage = COMPUTE_LOOP_INV;
  ref<Expr> invPostHavoc = executor.computeLambda(state, f, lambda_arguments);
  state.syt_stage = tmp;
  executor.addConstraintGuarded(state, invPostHavoc);
}

void SpecialFunctionHandler::handleTpotSwitchOld(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  assert(state.computeOldValues == false);
  state.computeOldValues = true;
}
void SpecialFunctionHandler::handleTpotSwitchNew(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  assert(state.computeOldValues == true);
  state.computeOldValues = false;
}

void SpecialFunctionHandler::handleTpotUninterpreted(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 && "invalid number of arguments to tpot_uninterpreted");
  CallInst *ci = dyn_cast<CallInst>(target->inst);
  assert(ci && "tpot_names_obj_forall called with non-call instruction");
  llvm::Function *f_ptr = executor.getTargetFunction(ci->getOperand(0), state);
  assert(f_ptr && "The first argument to tpot_names_obj_forall is not a function pointer");

  executor.addUninterpretedFunction(f_ptr);
}

void SpecialFunctionHandler::handleTpotMalloc(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  static int malloc_idx = 0;                            
  assert(arguments.size()==1 && "invalid number of arguments to tpot_malloc");

  ref<BitVecExpr> e = BitVecExpr::create("tpot_malloc_ptr." + std::to_string(malloc_idx), 64);

  ref<Expr> mallocSize = arguments[0];

  __handleTpotPointsTo(state, target, e,
     "tpot_malloc_block." + std::to_string(malloc_idx++), mallocSize);

  // The return vale of points_to will be written to target.
  ref<Expr> pointsTo = executor.getDestCell(state, target).value;
  ref<Expr> ptrPositive = UgtExpr::create(e, ConstantExpr::create(0, 64));
  ref<Expr> constr = AndExpr::create(pointsTo, ptrPositive);
  
  bool res;
  bool success __attribute__((unused)) = executor.solver->mustBeFalse(
      state.getConstraints(true), constr, res, state.queryMetaData);
  assert(success && "FIXME: Unhandled solver failure");
  if (res) {
    assert(0 && "allocations constraints are unsatisfiable.");
  } else {
    executor.addConstraintGuarded(state, constr);
  }
  executor.bindLocal(target, state, e);
}

void SpecialFunctionHandler::handleTpotFree(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 && "invalid number of arguments to tpot_free");
  NoOpResolutionList rl = executor.resolveAddressNoOp(state, arguments[0], NULL, NULL, 0, "");
  assert(rl.isSingleResolution() && "multiple resolution in tpot_free");
  const MemoryObject *mo = rl.objects[0].first;
  assert(mo && "First argument does not resolve to an object");

  // must be a heap object
  assert(mo->address == 0 && !mo->uniqueHeapAddress.isNull());
  
  // get the objectState
  const ObjectState *os = state.heap.findObject(mo);
  // must be a SSObjectState. 
  const SytSSObjectState *ssos = dynamic_cast<const SytSSObjectState *>(os);
  assert(ssos && "tpot_free called on non-SSObjectState object");

  // free the object
  if (ssos->isFreed) {
    executor.terminateStateOnUserError(state, "double free");
  } else {
    ObjectState *wos = state.heap.getWriteable(mo, os);
    // sigh.. cast & check again.
    SytSSObjectState *wssos = dynamic_cast< SytSSObjectState *>(wos);
    assert(wssos && "tpot_free called on non-SSObjectState object");
    wssos->isFreed = true;
  }
}

void SpecialFunctionHandler::handleUninterpFunc(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments,
                            llvm::Function *f) {
  // sanity checks
  const FunctionType *fType =  dyn_cast<FunctionType>(
      cast<PointerType>(f->getType())->getElementType());
  unsigned numParams = fType->getNumParams();
  assert(numParams == arguments.size() && "invalid number of arguments to uninterpreted function");
  for (unsigned i = 0; i < numParams; i++) {
    Type *paramType = fType->getParamType(i);
    assert(executor.getWidthForLLVMType(paramType) == arguments[i]->getWidth() && 
    "uninterpreted function called with wrong argument type");
  }

  ref<Expr> res = FuncAppExpr::create(f->getName().str(), arguments);
  executor.bindLocal(target, state, res);
}

void SpecialFunctionHandler::handleTpotAssertUnchangedExcept(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  // sanity checks
  assert(arguments.size() % 2 == 0 && "invalid number of arguments to assert_unchanged_except");
  unsigned numParams = arguments.size() / 2;
  for (unsigned i = 0; i < numParams; i++) {
    assert(arguments[2*i]->getWidth() == Expr::Int64 && "invalid argument (expected pointer)");
  }

  for (auto obj : state.modifiedGlobals) {
    bool inHeap = true;
    const ObjectState *os = state.heap.findObject(obj);
    if (!os) {
      os = state.addressSpace.findObject(obj);
      inHeap = false;
    }
    if (!os) {
      // the object is in a havoc layer.
      for (int i = 0; i < state.activeInvariants.size(); i++) {
        os = state.activeInvariants[i].heap->findObject(obj);
        if (os) {
          inHeap = true;
          break;
        }
        os = state.activeInvariants[i].addressSpace->findObject(obj);
        if (os) {
          break;
        }
      }
    }

    ref<UpdateNode> curUpdate = os->updates.head;
    while (curUpdate) {
      ref<Expr> storeIdx = curUpdate->index;
      ref<Expr> storeAddr;
      if (inHeap) {
        storeAddr = AddExpr::create(obj->uniqueHeapAddress, storeIdx);
      } else {
        storeAddr = AddExpr::create(ConstantExpr::create(obj->address, 64), storeIdx);
      }
      // check if this store was allowed in the except list
      bool allowed = false;
      for (unsigned i = 0; i < numParams; i++) {
        ref<Expr> exceptPtr = arguments[2*i];
        ref<Expr> exceptSize = arguments[2*i + 1];
        if (inHeap) {
          exceptPtr = executor.convertToInteger(state, exceptPtr);
          exceptSize = executor.convertToInteger(state, exceptSize);
        }
        ref<Expr> exceptEnd = AddExpr::create(exceptPtr, exceptSize);
        ref<Expr> fits = AndExpr::create(
          UleExpr::create(exceptPtr, storeAddr),
          UltExpr::create(storeAddr, exceptEnd)
        );
        
        bool res;
        bool success __attribute__((unused)) = executor.solver->mustBeTrue(
        state.getConstraints(/*useHeapConstraints=*/true), fits, res, state.queryMetaData);
        if (res) {
          allowed = true;
          break;
        }
      }
      if (!allowed) {
        executor.terminateStateOnUserError(state, "assert_unchanged_except failed");
      }
      curUpdate = curUpdate->next;
    }
  }
}

// ------------------------- //

void SpecialFunctionHandler::handleMemset(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  assert(0); // should never be called.                              
  // klee_warning("Invoked dummy SyT handler for memset. This is a no-op");

  // /* do nothing */

  // // return dst
  // executor.bindLocal(target, state, arguments[0]);
}

// This handles the fixed-size memcpy's inserted into th IR by Clang for freestanding binaries.
void SpecialFunctionHandler::handleMemcpy(ExecutionState &state,
                                          KInstruction *target,
                                          std::vector<ref<Expr>> &arguments) {
  // tpot_message("TPoT memcpy fast path");
  assert(arguments.size() == 3 && "invalid number of arguments to memcpy");
  // target->inst->dump();
  ref<Expr> destination = arguments[0];
  ref<Expr> source = arguments[1];
  const ref<ConstantExpr> size = dyn_cast<ConstantExpr>(arguments[2]);

  if (!size.get()) {
    tpot_message("Variable size memcpy not supported yet");
    executor.bindLocal(target, state, ConstantExpr::create(0, Expr::Int8));
    return;
  }

  uint64_t sizeVal = size->getZExtValue();
  if (sizeVal == 0) {
    executor.bindLocal(target, state, ConstantExpr::create(1, Expr::Int8));
    return;
  }
  // tpot_message("TPoT memcpy, size = %lu", sizeVal);

  // TODO: check they are in the same object

  NoOpResolutionList rl =
      executor.resolveAddressNoOp(state, source, NULL, NULL, 0, "");
  assert(rl.objects.size() == 1);
  const MemoryObject *source_mo = rl.objects.begin()->first;
  const ObjectState *source_os = state.addressSpace.findObject(source_mo)
                                     ? state.addressSpace.findObject(source_mo)
                                     : state.heap.findObject(source_mo);
  rl = executor.resolveAddressNoOp(state, destination, NULL, NULL, 0, "");
  assert(rl.objects.size() == 1);
  const MemoryObject *destination_mo = rl.objects.begin()->first;
  // assert(dynamic_cast<const SytSSMemoryObject *>(destination_mo) != NULL);
  const ObjectState *destination_os =
      state.addressSpace.findObject(destination_mo)
          ? state.addressSpace.findObject(destination_mo)
          : state.heap.findObject(destination_mo);
  ObjectState *writeable_destination_os;
  if (state.addressSpace.findObject(destination_mo)) {
    writeable_destination_os =
        state.addressSpace.getWriteable(destination_mo, destination_os);
  } else {
    writeable_destination_os =
        state.heap.getWriteable(destination_mo, destination_os);
  }

  // source = executor.convertToInteger(state, source);
  // destination = executor.convertToInteger(state, destination);
  // std::vector<ref<Expr>> unsignedExprs;
  Expr::Width type = Expr::Int8;
  for (unsigned i = 0; i < sizeVal; i++) {
    ref<Expr> tmp_source = AddExpr::create(source, ConstantExpr::create(i, 64));
    tmp_source = executor.convertToInteger(state, tmp_source);
    ref<Expr> relative_address = tmp_source;
    if (source_mo->uniqueHeapAddress)
      relative_address =
          SubExpr::create(tmp_source, source_mo->uniqueHeapAddress);

    ref<Expr> offset = source_mo->getOffsetExpr(relative_address);
    ref<Expr> value = source_os->read(
        offset, type, state.computeOldValues && !source_mo->isLocal);
    if (executor.interpreterOpts.MakeConcreteSymbolic) {
      value = executor.replaceReadWithSymbolic(state, value);
    }
    if (!source_mo->forallElem.empty() &&
        i == sizeVal - 1) { // only instantiate for the last byte
      executor.instantiateForallElem(state, source_mo, offset, tmp_source);
    }
    assert(value->getWidth() == 8);

    // TODO: this seems ugly
    ref<Expr> tmp_destination =
        AddExpr::create(destination, ConstantExpr::create(i, 64));
    tmp_destination = executor.convertToInteger(state, tmp_destination);
    relative_address = tmp_destination;
    if (destination_mo->uniqueHeapAddress)
      relative_address =
          SubExpr::create(tmp_destination, destination_mo->uniqueHeapAddress);

    offset = destination_mo->getOffsetExpr(relative_address);
    writeable_destination_os->write(offset, value);
    if (!destination_mo->forallElem.empty() &&
        i == sizeVal - 1) { // only instantiate for the last byte
      executor.instantiateForallElem(state, destination_mo, offset, tmp_source);
    }
  }

  executor.bindLocal(target, state, ConstantExpr::create(0, Expr::Int8));
}

void SpecialFunctionHandler::handleSkipInvariantCheck(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  assert(0); // This should not be called.
  // tpot_message(
  //     "skip invariant check called, will skip invariant check for state: %d",
  //     state.id);
  // state.skipInvariantChecks = true;
}

void SpecialFunctionHandler::handleDebugPrint(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 1 && "invalid number of arguments to debug_print");
  ref<Expr> message = arguments[0];
  std::string message_str = readStringAtAddress(state, message);
  tpot_message("Debug print: %s", message_str.c_str());
}