//===-- Executor.cpp ------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "Executor.h"
#include "Context.h"
#include "CoreStats.h"
#include "ExecutionState.h"
#include "ExternalDispatcher.h"
#include "GetElementPtrTypeIterator.h"
#include "ImpliedValue.h"
#include "Memory.h"
#include "MemoryManager.h"
#include "PTree.h"
#include "Searcher.h"
#include "SeedInfo.h"
#include "SpecialFunctionHandler.h"
#include "StatsTracker.h"
#include "TimingSolver.h"
#include "UserSearcher.h"

#include "../Solver/SytZ3Dumper.h"

#include "klee/ADT/KTest.h"
#include "klee/ADT/RNG.h"
#include "klee/Config/Version.h"
#include "klee/Core/BranchTypes.h"
#include "klee/Core/Interpreter.h"
#include "klee/Expr/ArrayExprOptimizer.h"
#include "klee/Expr/Assignment.h"
#include "klee/Expr/Constraints.h"
#include "klee/Expr/Expr.h"
#include "klee/Expr/ExprPPrinter.h"
#include "klee/Expr/ExprSMTLIBPrinter.h"
#include "klee/Expr/ExprUtil.h"
#include "klee/Module/Cell.h"
#include "klee/Module/InstructionInfoTable.h"
#include "klee/Module/KInstruction.h"
#include "klee/Module/KModule.h"
#include "klee/Solver/Common.h"
#include "klee/Solver/SolverCmdLine.h"
#include "klee/Solver/SolverStats.h"
#include "klee/Solver/SolverImpl.h"
#include "klee/Statistics/TimerStatIncrementer.h"
#include "klee/Support/Casting.h"
#include "klee/Support/ErrorHandling.h"
#include "klee/Support/FileHandling.h"
#include "klee/Support/FloatEvaluation.h"
#include "klee/Support/ModuleUtil.h"
#include "klee/Support/OptionCategories.h"
#include "klee/System/MemoryUsage.h"
#include "klee/System/Time.h"

#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#if LLVM_VERSION_CODE < LLVM_VERSION(8, 0)
#include "llvm/IR/CallSite.h"
#endif
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/Process.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(10, 0)
#include "llvm/Support/TypeSize.h"
#else
typedef unsigned TypeSize;
#endif
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Dominators.h"


#include <algorithm>
#include <cassert>
#include <cerrno>
#include <cstring>
#include <cxxabi.h>
#include <fstream>
#include <iomanip>
#include <iosfwd>
#include <limits>
#include <sstream>
#include <string>
#include <sys/mman.h>
#include <vector>
#include <iostream>

#include <signal.h> // SIGINT

using namespace llvm;
using namespace klee;

// SyT Extensions
#define SYT_INIT_GLOBALS_SYMB



namespace klee {
cl::OptionCategory DebugCat("Debugging options",
                            "These are debugging options.");

cl::OptionCategory ExtCallsCat("External call policy options",
                               "These options impact external calls.");

cl::OptionCategory SeedingCat(
    "Seeding options",
    "These options are related to the use of seeds to start exploration.");

cl::OptionCategory
    TerminationCat("State and overall termination options",
                   "These options control termination of the overall KLEE "
                   "execution and of individual states.");

cl::OptionCategory TestGenCat("Test generation options",
                              "These options impact test generation.");

cl::OptionCategory SytCat("SyT options",
                              "These options toggle SyT extensions.");

cl::opt<std::string> MaxTime(
    "max-time",
    cl::desc("Halt execution after the specified duration.  "
             "Set to 0s to disable (default=0s)"),
    cl::init("0s"),
    cl::cat(TerminationCat));
} // namespace klee

namespace {

/*** Test generation options ***/

cl::opt<bool> DumpStatesOnHalt(
    "dump-states-on-halt",
    cl::init(true),
    cl::desc("Dump test cases for all active states on exit (default=true)"),
    cl::cat(TestGenCat));

cl::opt<bool> OnlyOutputStatesCoveringNew(
    "only-output-states-covering-new",
    cl::init(false),
    cl::desc("Only output test cases covering new code (default=false)"),
    cl::cat(TestGenCat));

cl::opt<bool> EmitAllErrors(
    "emit-all-errors", cl::init(false),
    cl::desc("Generate tests cases for all errors "
             "(default=false, i.e. one per (error,instruction) pair)"),
    cl::cat(TestGenCat));


/* Constraint solving options */

cl::opt<unsigned> MaxSymArraySize(
    "max-sym-array-size",
    cl::desc(
        "If a symbolic array exceeds this size (in bytes), symbolic addresses "
        "into this array are concretized.  Set to 0 to disable (default=0)"),
    cl::init(0),
    cl::cat(SolvingCat));

cl::opt<bool>
    SimplifySymIndices("simplify-sym-indices",
                       cl::init(false),
                       cl::desc("Simplify symbolic accesses using equalities "
                                "from other constraints (default=false)"),
                       cl::cat(SolvingCat));

cl::opt<bool>
    EqualitySubstitution("equality-substitution", cl::init(true),
                         cl::desc("Simplify equality expressions before "
                                  "querying the solver (default=true)"),
                         cl::cat(SolvingCat));


/*** External call policy options ***/

enum class ExternalCallPolicy {
  None,     // No external calls allowed
  Concrete, // Only external calls with concrete arguments allowed
  All,      // All external calls allowed
};

cl::opt<ExternalCallPolicy> ExternalCalls(
    "external-calls",
    cl::desc("Specify the external call policy"),
    cl::values(
        clEnumValN(
            ExternalCallPolicy::None, "none",
            "No external function calls are allowed.  Note that KLEE always "
            "allows some external calls with concrete arguments to go through "
            "(in particular printf and puts), regardless of this option."),
        clEnumValN(ExternalCallPolicy::Concrete, "concrete",
                   "Only external function calls with concrete arguments are "
                   "allowed (default)"),
        clEnumValN(ExternalCallPolicy::All, "all",
                   "All external function calls are allowed.  This concretizes "
                   "any symbolic arguments in calls to external functions.")),
    cl::init(ExternalCallPolicy::Concrete),
    cl::cat(ExtCallsCat));

cl::opt<bool> SuppressExternalWarnings(
    "suppress-external-warnings",
    cl::init(false),
    cl::desc("Supress warnings about calling external functions."),
    cl::cat(ExtCallsCat));

cl::opt<bool> AllExternalWarnings(
    "all-external-warnings",
    cl::init(false),
    cl::desc("Issue a warning everytime an external call is made, "
             "as opposed to once per function (default=false)"),
    cl::cat(ExtCallsCat));


/*** Seeding options ***/

cl::opt<bool> AlwaysOutputSeeds(
    "always-output-seeds",
    cl::init(true),
    cl::desc(
        "Dump test cases even if they are driven by seeds only (default=true)"),
    cl::cat(SeedingCat));

cl::opt<bool> OnlyReplaySeeds(
    "only-replay-seeds",
    cl::init(false),
    cl::desc("Discard states that do not have a seed (default=false)."),
    cl::cat(SeedingCat));

cl::opt<bool> OnlySeed("only-seed",
                       cl::init(false),
                       cl::desc("Stop execution after seeding is done without "
                                "doing regular search (default=false)."),
                       cl::cat(SeedingCat));

cl::opt<bool>
    AllowSeedExtension("allow-seed-extension",
                       cl::init(false),
                       cl::desc("Allow extra (unbound) values to become "
                                "symbolic during seeding (default=false)."),
                       cl::cat(SeedingCat));

cl::opt<bool> ZeroSeedExtension(
    "zero-seed-extension",
    cl::init(false),
    cl::desc(
        "Use zero-filled objects if matching seed not found (default=false)"),
    cl::cat(SeedingCat));

cl::opt<bool> AllowSeedTruncation(
    "allow-seed-truncation",
    cl::init(false),
    cl::desc("Allow smaller buffers than in seeds (default=false)."),
    cl::cat(SeedingCat));

cl::opt<bool> NamedSeedMatching(
    "named-seed-matching",
    cl::init(false),
    cl::desc("Use names to match symbolic objects to inputs (default=false)."),
    cl::cat(SeedingCat));

cl::opt<std::string>
    SeedTime("seed-time",
             cl::desc("Amount of time to dedicate to seeds, before normal "
                      "search (default=0s (off))"),
             cl::cat(SeedingCat));


/*** Termination criteria options ***/

cl::list<StateTerminationType> ExitOnErrorType(
    "exit-on-error-type",
    cl::desc("Stop execution after reaching a specified condition (default=false)"),
    cl::values(
        clEnumValN(StateTerminationType::Abort, "Abort",
                   "The program crashed (reached abort()/klee_abort())"),
        clEnumValN(StateTerminationType::Assert, "Assert",
                   "An assertion was hit"),
        clEnumValN(StateTerminationType::BadVectorAccess, "BadVectorAccess",
                   "Vector accessed out of bounds"),
        clEnumValN(StateTerminationType::Execution, "Execution",
                   "Trying to execute an unexpected instruction"),
        clEnumValN(StateTerminationType::External, "External",
                   "External objects referenced"),
        clEnumValN(StateTerminationType::Free, "Free",
                   "Freeing invalid memory"),
        clEnumValN(StateTerminationType::Model, "Model",
                   "Memory model limit hit"),
        clEnumValN(StateTerminationType::Overflow, "Overflow",
                   "An overflow occurred"),
        clEnumValN(StateTerminationType::Ptr, "Ptr", "Pointer error"),
        clEnumValN(StateTerminationType::ReadOnly, "ReadOnly",
                   "Write to read-only memory"),
        clEnumValN(StateTerminationType::ReportError, "ReportError",
                   "klee_report_error called"),
        clEnumValN(StateTerminationType::User, "User",
                   "Wrong klee_* functions invocation")),
    cl::ZeroOrMore,
    cl::cat(TerminationCat));

cl::opt<unsigned long long> MaxInstructions(
    "max-instructions",
    cl::desc("Stop execution after this many instructions.  Set to 0 to disable (default=0)"),
    cl::init(0),
    cl::cat(TerminationCat));

cl::opt<unsigned>
    MaxForks("max-forks",
             cl::desc("Only fork this many times.  Set to -1 to disable (default=-1)"),
             cl::init(~0u),
             cl::cat(TerminationCat));

cl::opt<unsigned> MaxDepth(
    "max-depth",
    cl::desc("Only allow this many symbolic branches.  Set to 0 to disable (default=0)"),
    cl::init(0),
    cl::cat(TerminationCat));

cl::opt<unsigned> MaxMemory("max-memory",
                            cl::desc("Refuse to fork when above this amount of "
                                     "memory (in MB) (see -max-memory-inhibit) and terminate "
                                     "states when additional 100MB allocated (default=2000)"),
                            cl::init(2000),
                            cl::cat(TerminationCat));

cl::opt<bool> MaxMemoryInhibit(
    "max-memory-inhibit",
    cl::desc(
        "Inhibit forking when above memory cap (see -max-memory) (default=true)"),
    cl::init(true),
    cl::cat(TerminationCat));

cl::opt<unsigned> RuntimeMaxStackFrames(
    "max-stack-frames",
    cl::desc("Terminate a state after this many stack frames.  Set to 0 to "
             "disable (default=8192)"),
    cl::init(8192),
    cl::cat(TerminationCat));

cl::opt<double> MaxStaticForkPct(
    "max-static-fork-pct", cl::init(1.),
    cl::desc("Maximum percentage spent by an instruction forking out of the "
             "forking of all instructions (default=1.0 (always))"),
    cl::cat(TerminationCat));

cl::opt<double> MaxStaticSolvePct(
    "max-static-solve-pct", cl::init(1.),
    cl::desc("Maximum percentage of solving time that can be spent by a single "
             "instruction over total solving time for all instructions "
             "(default=1.0 (always))"),
    cl::cat(TerminationCat));

cl::opt<double> MaxStaticCPForkPct(
    "max-static-cpfork-pct", cl::init(1.),
    cl::desc("Maximum percentage spent by an instruction of a call path "
             "forking out of the forking of all instructions in the call path "
             "(default=1.0 (always))"),
    cl::cat(TerminationCat));

cl::opt<double> MaxStaticCPSolvePct(
    "max-static-cpsolve-pct", cl::init(1.),
    cl::desc("Maximum percentage of solving time that can be spent by a single "
             "instruction of a call path over total solving time for all "
             "instructions (default=1.0 (always))"),
    cl::cat(TerminationCat));

cl::opt<unsigned> MaxStaticPctCheckDelay(
    "max-static-pct-check-delay",
    cl::desc("Number of forks after which the --max-static-*-pct checks are enforced (default=1000)"),
    cl::init(1000),
    cl::cat(TerminationCat));

cl::opt<std::string> TimerInterval(
    "timer-interval",
    cl::desc("Minimum interval to check timers. "
             "Affects -max-time, -istats-write-interval, -stats-write-interval, and -uncovered-update-interval (default=1s)"),
    cl::init("1s"),
    cl::cat(TerminationCat));


/*** Debugging options ***/

/// The different query logging solvers that can switched on/off
enum PrintDebugInstructionsType {
  STDERR_ALL, ///
  STDERR_SRC,
  STDERR_COMPACT,
  FILE_ALL,    ///
  FILE_SRC,    ///
  FILE_COMPACT ///
};

llvm::cl::bits<PrintDebugInstructionsType> DebugPrintInstructions(
    "debug-print-instructions",
    llvm::cl::desc("Log instructions during execution."),
    llvm::cl::values(
        clEnumValN(STDERR_ALL, "all:stderr",
                   "Log all instructions to stderr "
                   "in format [src, inst_id, "
                   "llvm_inst]"),
        clEnumValN(STDERR_SRC, "src:stderr",
                   "Log all instructions to stderr in format [src, inst_id]"),
        clEnumValN(STDERR_COMPACT, "compact:stderr",
                   "Log all instructions to stderr in format [inst_id]"),
        clEnumValN(FILE_ALL, "all:file",
                   "Log all instructions to file "
                   "instructions.txt in format [src, "
                   "inst_id, llvm_inst]"),
        clEnumValN(FILE_SRC, "src:file",
                   "Log all instructions to file "
                   "instructions.txt in format [src, "
                   "inst_id]"),
        clEnumValN(FILE_COMPACT, "compact:file",
                   "Log all instructions to file instructions.txt in format "
                   "[inst_id]")),
    llvm::cl::CommaSeparated,
    cl::cat(DebugCat));

/* Syt options */
cl::opt<bool> InductiveSymbex(
    "inductive-symbex", cl::init(false),
    cl::desc(
        "Enable inductive reasoning over loops (default=false)."),
    cl::cat(SytCat));

cl::opt<bool> AssumeGlobalInvariants(
    "assume-global-invs", cl::init(true),
    cl::desc(
        "Assume global invariants. Disable if verifying an initializer (default=true) ."),
    cl::cat(SytCat));

cl::opt<bool> AssertGlobalInvariants(
    "assert-global-invs", cl::init(true),
    cl::desc(
        "Assert global invariants (default=true)."),
    cl::cat(SytCat));
cl::opt<bool> EnableFailingCodePath(
    "enable-failing-code-path", cl::init(false),
    cl::desc("Enable code-path retrieval on assertion or invariant failure"),
    cl::cat(SytCat));

cl::opt<bool>
    CheckBranchBothIntBV("check-branch-both-int-bv", cl::init(false),
                         cl::desc("Check the branch for both integer and bv."),
                         cl::cat(SytCat));
cl::opt<bool> AnnotateSMT(
    "annotate-smt", cl::init(false),
    cl::desc(
        "Annotate the SMT formula with the source location the assertion results from. (default=false)."),
    cl::cat(SytCat));

cl::opt<bool> UseInvCheckShortcuts(
    "inv-check-shortcuts", cl::init(false),
    cl::desc(
        "Avoid checking invariants that only read unmodified data (default=false)."),
    cl::cat(SytCat));
cl::opt<bool>
    TpotOptimizeGlobalArrays("tpot-opt-global-arrs", cl::init(true),
                         cl::desc("Use optimized heap representation for global arrays"),
                         cl::cat(SytCat));

#ifdef HAVE_ZLIB_H
cl::opt<bool> DebugCompressInstructions(
    "debug-compress-instructions", cl::init(false),
    cl::desc(
        "Compress the logged instructions in gzip format (default=false)."),
    cl::cat(DebugCat));
#endif

cl::opt<bool> DebugCheckForImpliedValues(
    "debug-check-for-implied-values", cl::init(false),
    cl::desc("Debug the implied value optimization"),
    cl::cat(DebugCat));

} // namespace

// XXX hack
extern "C" unsigned dumpStates, dumpPTree;
unsigned dumpStates = 0, dumpPTree = 0;

void Executor::initializeSolver(std::string sytInitConstraints) {
  coreSolverTimeout = time::Span{MaxCoreSolverTime};
  if (coreSolverTimeout) UseForkedCoreSolver = true;
  Solver *coreSolver = klee::createCoreSolver(CoreSolverToUse, sytInitConstraints);
  if (!coreSolver) {
    klee_error("Failed to create core solver\n");
  }

  Solver *solver = constructSolverChain(
      coreSolver,
      interpreterHandler->getOutputFilename(ALL_QUERIES_SMT2_FILE_NAME),
      interpreterHandler->getOutputFilename(SOLVER_QUERIES_SMT2_FILE_NAME),
      interpreterHandler->getOutputFilename(ALL_QUERIES_KQUERY_FILE_NAME),
      interpreterHandler->getOutputFilename(SOLVER_QUERIES_KQUERY_FILE_NAME),
      sytInitConstraints);

  this->solver = new TimingSolver(solver, EqualitySubstitution);
}

Executor::Executor(LLVMContext &ctx, const InterpreterOptions &opts,
                   InterpreterHandler *ih, std::string sytInitConstraints)
    : Interpreter(opts), interpreterHandler(ih), searcher(0),
      externalDispatcher(new ExternalDispatcher(ctx)), statsTracker(0),
      pathWriter(0), symPathWriter(0), specialFunctionHandler(0), timers{time::Span(TimerInterval)},
      replayKTest(0), replayPath(0), usingSeeds(0),
      atMemoryLimit(false), inhibitForking(false), haltExecution(false),
      ivcEnabled(false), debugLogBuffer(debugBufferString), isSmokeTest(false) {


  const time::Span maxTime{MaxTime};
  if (maxTime) timers.add(
        std::make_unique<Timer>(maxTime, [&]{
        klee_message("HaltTimer invoked");
        setHaltExecution(true);
      }));

  // define all smt functions we need before constructing the solver.
  initSMTFuncs();

  // TPOT: initialize the solver after setModule in order to account for
  // uninterpreted functions introduced by the target.

  // coreSolverTimeout = time::Span{MaxCoreSolverTime};
  // if (coreSolverTimeout) UseForkedCoreSolver = true;
  // Solver *coreSolver = klee::createCoreSolver(CoreSolverToUse, sytInitConstraints);
  // if (!coreSolver) {
  //   klee_error("Failed to create core solver\n");
  // }

  // Solver *solver = constructSolverChain(
  //     coreSolver,
  //     interpreterHandler->getOutputFilename(ALL_QUERIES_SMT2_FILE_NAME),
  //     interpreterHandler->getOutputFilename(SOLVER_QUERIES_SMT2_FILE_NAME),
  //     interpreterHandler->getOutputFilename(ALL_QUERIES_KQUERY_FILE_NAME),
  //     interpreterHandler->getOutputFilename(SOLVER_QUERIES_KQUERY_FILE_NAME),
  //     sytInitConstraints);

  // this->solver = new TimingSolver(solver, EqualitySubstitution);
  this->sytPostStateSolver = NULL;
  memory = new MemoryManager(&arrayCache);

  initializeSearchOptions();

  if (OnlyOutputStatesCoveringNew && !StatsTracker::useIStats())
    klee_error("To use --only-output-states-covering-new, you need to enable --output-istats.");

  if (DebugPrintInstructions.isSet(FILE_ALL) ||
      DebugPrintInstructions.isSet(FILE_COMPACT) ||
      DebugPrintInstructions.isSet(FILE_SRC)) {
    std::string debug_file_name =
        interpreterHandler->getOutputFilename("instructions.txt");
    std::string error;
#ifdef HAVE_ZLIB_H
    if (!DebugCompressInstructions) {
#endif
      debugInstFile = klee_open_output_file(debug_file_name, error);
#ifdef HAVE_ZLIB_H
    } else {
      debug_file_name.append(".gz");
      debugInstFile = klee_open_compressed_output_file(debug_file_name, error);
    }
#endif
    if (!debugInstFile) {
      klee_error("Could not open file %s : %s", debug_file_name.c_str(),
                 error.c_str());
    }
  }
}

void Executor::setSytPostConstraints(std::string filename) {
  sytPostStateSolver = new SytZ3Dumper(filename, filename + ".modified_fields");
}

llvm::Module *
Executor::setModule(std::vector<std::unique_ptr<llvm::Module>> &modules,
                    const ModuleOptions &opts) {
  assert(!kmodule && !modules.empty() &&
         "can only register one module"); // XXX gross

  kmodule = std::unique_ptr<KModule>(new KModule());

  // Preparing the final module happens in multiple stages

  // Link with KLEE intrinsics library before running any optimizations
  SmallString<128> LibPath(opts.LibraryDir);
  llvm::sys::path::append(LibPath,
                          "libkleeRuntimeIntrinsic" + opts.OptSuffix + ".bca");
  std::string error;
  if (!klee::loadFile(LibPath.c_str(), modules[0]->getContext(), modules,
                      error)) {
    klee_error("Could not load KLEE intrinsic file %s", LibPath.c_str());
  }

  // 1.) Link the modules together
  while (kmodule->link(modules, opts.EntryPoint)) {
    // 2.) Apply different instrumentation
    kmodule->instrument(opts);
  }

  // 3.) Optimise and prepare for KLEE

  // Create a list of functions that should be preserved if used
  std::vector<const char *> preservedFunctions;
  specialFunctionHandler = new SpecialFunctionHandler(*this);
  specialFunctionHandler->prepare(preservedFunctions);

  preservedFunctions.push_back(opts.EntryPoint.c_str());

  // Preserve the free-standing library calls
  preservedFunctions.push_back("memset");
  preservedFunctions.push_back("memcpy");
  preservedFunctions.push_back("memcmp");
  preservedFunctions.push_back("memmove");

  kmodule->optimiseAndPrepare(opts, preservedFunctions);
  kmodule->checkModule();

  // 4.) Manifest the module
  kmodule->manifest(interpreterHandler, StatsTracker::useStatistics());

  kmodule->identifyLoops();
  for (auto f : kmodule->uninterpFunctions) {
    addUninterpretedFunction(f);
  }

  specialFunctionHandler->bind();

  if (StatsTracker::useStatistics() || userSearcherRequiresMD2U()) {
    statsTracker = 
      new StatsTracker(*this,
                       interpreterHandler->getOutputFilename("assembly.ll"),
                       userSearcherRequiresMD2U());
  }

  // Initialize the context.
  DataLayout *TD = kmodule->targetData.get();
  Context::initialize(TD->isLittleEndian(),
                      (Expr::Width)TD->getPointerSizeInBits());

  return kmodule->module.get();
}

Executor::~Executor() {
  delete memory;
  delete externalDispatcher;
  delete specialFunctionHandler;
  delete statsTracker;
  delete solver;
}

/***/

void Executor::initializeGlobalObject(ExecutionState &state, ObjectState *os,
                                      const Constant *c, 
                                      unsigned offset) {
  const auto targetData = kmodule->targetData.get();
  if (const ConstantVector *cp = dyn_cast<ConstantVector>(c)) {
    unsigned elementSize =
      targetData->getTypeStoreSize(cp->getType()->getElementType());
    for (unsigned i=0, e=cp->getNumOperands(); i != e; ++i)
      initializeGlobalObject(state, os, cp->getOperand(i), 
			     offset + i*elementSize);
  } else if (isa<ConstantAggregateZero>(c)) {
    unsigned i, size = targetData->getTypeStoreSize(c->getType());
    for (i=0; i<size; i++)
      os->write8(offset+i, (uint8_t) 0);
  } else if (const ConstantArray *ca = dyn_cast<ConstantArray>(c)) {
    unsigned elementSize =
      targetData->getTypeStoreSize(ca->getType()->getElementType());
    for (unsigned i=0, e=ca->getNumOperands(); i != e; ++i)
      initializeGlobalObject(state, os, ca->getOperand(i), 
			     offset + i*elementSize);
  } else if (const ConstantStruct *cs = dyn_cast<ConstantStruct>(c)) {
    const StructLayout *sl =
      targetData->getStructLayout(cast<StructType>(cs->getType()));
    for (unsigned i=0, e=cs->getNumOperands(); i != e; ++i)
      initializeGlobalObject(state, os, cs->getOperand(i), 
			     offset + sl->getElementOffset(i));
  } else if (const ConstantDataSequential *cds =
               dyn_cast<ConstantDataSequential>(c)) {
    unsigned elementSize =
      targetData->getTypeStoreSize(cds->getElementType());
    for (unsigned i=0, e=cds->getNumElements(); i != e; ++i)
      initializeGlobalObject(state, os, cds->getElementAsConstant(i),
                             offset + i*elementSize);
  } else if (!isa<UndefValue>(c) && !isa<MetadataAsValue>(c)) {
    unsigned StoreBits = targetData->getTypeStoreSizeInBits(c->getType());
    ref<ConstantExpr> C = evalConstant(c);

    // Extend the constant if necessary;
    assert(StoreBits >= C->getWidth() && "Invalid store size!");
    if (StoreBits > C->getWidth())
      C = C->ZExt(StoreBits);

    os->write(offset, C);
  }
}

MemoryObject * Executor::addExternalObject(ExecutionState &state, 
                                           void *addr, unsigned size, 
                                           bool isReadOnly) {
  auto mo = memory->allocateFixed(reinterpret_cast<std::uint64_t>(addr),
                                  size, nullptr);
  ObjectState *os = bindObjectInState(state, mo, false);
  for(unsigned i = 0; i < size; i++)
    os->write8(i, ((uint8_t*)addr)[i]);
  if(isReadOnly)
    os->setReadOnly(true);  
  return mo;
}


extern void *__dso_handle __attribute__ ((__weak__));

void Executor::initializeGlobals(ExecutionState &state) {
  // allocate and initialize globals, done in two passes since we may
  // need address of a global in order to initialize some other one.

  // allocate memory objects for all globals
  allocateGlobalObjects(state);

  // initialize aliases first, may be needed for global objects
  initializeGlobalAliases();

  // finally, do the actual initialization
  initializeGlobalObjects(state);
}

void Executor::allocateGlobalObjects(ExecutionState &state) {
  Module *m = kmodule->module.get();

  if (m->getModuleInlineAsm() != "")
    klee_warning("executable has module level assembly (ignoring)");
  // represent function globals using the address of the actual llvm function
  // object. given that we use malloc to allocate memory in states this also
  // ensures that we won't conflict. we don't need to allocate a memory object
  // since reading/writing via a function pointer is unsupported anyway.
  for (Function &f : *m) {
    ref<ConstantExpr> addr;

    // If the symbol has external weak linkage then it is implicitly
    // not defined in this module; if it isn't resolvable then it
    // should be null.
    if (f.hasExternalWeakLinkage() &&
        !externalDispatcher->resolveSymbol(f.getName().str())) {
      addr = Expr::createPointer(0);
    } else {
      // We allocate an object to represent each function,
      // its address can be used for function pointers.
      // TODO: Check whether the object is accessed?
      auto mo = memory->allocate(8, false, true, &f, 8);
      addr = Expr::createPointer(mo->address);
      legalFunctions.emplace(mo->address, &f);
    }

    globalAddresses.emplace(&f, addr);
  }

#ifndef WINDOWS
  int *errno_addr = getErrnoLocation(state);
  MemoryObject *errnoObj =
      addExternalObject(state, (void *)errno_addr, sizeof *errno_addr, false);
  // Copy values from and to program space explicitly
  errnoObj->isUserSpecified = true;
#endif

  // Disabled, we don't want to promote use of live externals.
#ifdef HAVE_CTYPE_EXTERNALS
#ifndef WINDOWS
#ifndef DARWIN
  /* from /usr/include/ctype.h:
       These point into arrays of 384, so they can be indexed by any `unsigned
       char' value [0,255]; by EOF (-1); or by any `signed char' value
       [-128,-1).  ISO C requires that the ctype functions work for `unsigned */
  const uint16_t **addr = __ctype_b_loc();
  addExternalObject(state, const_cast<uint16_t*>(*addr-128),
                    384 * sizeof **addr, true);
  addExternalObject(state, addr, sizeof(*addr), true);
    
  const int32_t **lower_addr = __ctype_tolower_loc();
  addExternalObject(state, const_cast<int32_t*>(*lower_addr-128),
                    384 * sizeof **lower_addr, true);
  addExternalObject(state, lower_addr, sizeof(*lower_addr), true);
  
  const int32_t **upper_addr = __ctype_toupper_loc();
  addExternalObject(state, const_cast<int32_t*>(*upper_addr-128),
                    384 * sizeof **upper_addr, true);
  addExternalObject(state, upper_addr, sizeof(*upper_addr), true);
#endif
#endif
#endif

  for (const GlobalVariable &v : m->globals()) {
    std::size_t globalObjectAlignment = getAllocationAlignment(&v);
    Type *ty = v.getType()->getElementType();
    std::uint64_t size = 0;
    if (ty->isSized())
      size = kmodule->targetData->getTypeStoreSize(ty);

    if (v.isDeclaration()) {
      // FIXME: We have no general way of handling unknown external
      // symbols. If we really cared about making external stuff work
      // better we could support user definition, or use the EXE style
      // hack where we check the object file information.

      if (!ty->isSized()) {
        klee_warning("Type for %.*s is not sized",
                     static_cast<int>(v.getName().size()), v.getName().data());
      }

      // XXX - DWD - hardcode some things until we decide how to fix.
#ifndef WINDOWS
      if (v.getName() == "_ZTVN10__cxxabiv117__class_type_infoE") {
        size = 0x2C;
      } else if (v.getName() == "_ZTVN10__cxxabiv120__si_class_type_infoE") {
        size = 0x2C;
      } else if (v.getName() == "_ZTVN10__cxxabiv121__vmi_class_type_infoE") {
        size = 0x2C;
      }
#endif

      if (size == 0) {
        klee_warning("Unable to find size for global variable: %.*s (use will "
                     "result in out of bounds access)",
                     static_cast<int>(v.getName().size()), v.getName().data());
      }
    }

    MemoryObject *mo = memory->allocate(size, /*isLocal=*/false,
                                        /*isGlobal=*/true, /*allocSite=*/&v,
                                        /*alignment=*/globalObjectAlignment);
    if (!mo)
      klee_error("out of memory");
    globalObjects.emplace(&v, mo);
    globalAddresses.emplace(&v, mo->getBaseExpr());
  }
}

void Executor::initializeGlobalAlias(const llvm::Constant *c) {
  // aliasee may either be a global value or constant expression
  const auto *ga = dyn_cast<GlobalAlias>(c);
  if (ga) {
    if (globalAddresses.count(ga)) {
      // already resolved by previous invocation
      return;
    }
    const llvm::Constant *aliasee = ga->getAliasee();
    if (const auto *gv = dyn_cast<GlobalValue>(aliasee)) {
      // aliasee is global value
      auto it = globalAddresses.find(gv);
      // uninitialized only if aliasee is another global alias
      if (it != globalAddresses.end()) {
        globalAddresses.emplace(ga, it->second);
        return;
      }
    }
  }

  // resolve aliases in all sub-expressions
  for (const auto *op : c->operand_values()) {
    initializeGlobalAlias(cast<Constant>(op));
  }

  if (ga) {
    // aliasee is constant expression (or global alias)
    globalAddresses.emplace(ga, evalConstant(ga->getAliasee()));
  }
}

void Executor::initializeGlobalAliases() {
  const Module *m = kmodule->module.get();
  for (const GlobalAlias &a : m->aliases()) {
    initializeGlobalAlias(&a);
  }
}

void Executor::initializeGlobalObjects(ExecutionState &state) {
  const Module *m = kmodule->module.get();

  // remember constant objects to initialise their counter part for external
  // calls
  std::vector<ObjectState *> constantObjects;
  for (const GlobalVariable &v : m->globals()) {
    MemoryObject *mo = globalObjects.find(&v)->second;
    ObjectState *os = bindObjectInState(state, mo, false);

    if (v.isDeclaration() && mo->size) {
      // Program already running -> object already initialized.
      // Read concrete value and write it to our copy.
      void *addr;
      if (v.getName() == "__dso_handle") {
        addr = &__dso_handle; // wtf ?
      } else {
        addr = externalDispatcher->resolveSymbol(v.getName().str());
      }
      if (!addr) {
        klee_error("Unable to load symbol(%.*s) while initializing globals",
                   static_cast<int>(v.getName().size()), v.getName().data());
      }
      for (unsigned offset = 0; offset < mo->size; offset++) {
        os->write8(offset, static_cast<unsigned char *>(addr)[offset]);
      }
#ifdef SYT_INIT_GLOBALS_SYMB
    } else if (!v.isConstant() && !v.isDeclaration()){
      // Initialize global variables with symbolic values.
      // This excludes constants, which keep their value, and 
      // external objects.

      if (TpotOptimizeGlobalArrays && v.getType()->isPointerTy() &&
          v.getType()->getElementType()->isArrayTy()) {
        // optimization: if the global is an array, allocate it in the TPot heap
        // TPot's heap object repesentation deals with large objects more efficiently.
        auto name = "opt_globalarr__" + v.getName().str();
        ref<Expr> obj_addr_bvForm = specialFunctionHandler->allocateFreshBV64(
            state, std::string("addr__") + v.getName().str());
        ref<Expr> obj_addr = convertToInteger(state, obj_addr_bvForm);
        ref<Expr> obj_size = convertToInteger(state, ConstantExpr::create(mo->size, Expr::Int64));
        SytSSMemoryObject *optMo = new SytSSMemoryObject(/*address=*/0,
                                    /*size=*/obj_size,
                                    /*isLocal=*/false, /*isGlobal=*/true,
                                    false, /*allocSite=*/mo->allocSite,
                                    NULL, /*uniqueHeapAddress=*/obj_addr);
        optMo->isTpotGlobalArray = true;
        optMo->setName(name);
        specialFunctionHandler->allocateInHeap(state, optMo, obj_addr, obj_size, name, false);

        // Update the global tables.
        globalObjects[&v] = optMo;
        globalAddressesTpotWrapper[&v] = obj_addr_bvForm;
        
        // Need to adjust global aliases, too.
        for (const GlobalAlias &a : m->aliases()) {
          if (a.getAliasee() == &v) {
            globalAddressesTpotWrapper[&a] = obj_addr_bvForm;
          }
        }

        // Record the mapping between the original constant base and the new base,
        // so that we can substitute the new base.
        tpotGlobalAddressSubst[mo->address] = obj_addr_bvForm;

        // free(mo);
      } else {
        auto name = "syt_initval__" + v.getName().str();
        mo->setName(name);
        executeMakeSymbolic(state, mo, name);
      }

#endif
    } else if (v.hasInitializer()) {
      initializeGlobalObject(state, os, v.getInitializer(), 0);
      if (v.isConstant())
        constantObjects.emplace_back(os);
    } else {
      os->initializeToRandom();
    }

  }

  // initialise constant memory that is potentially used with external calls
  if (!constantObjects.empty()) {
    // initialise the actual memory with constant values
    state.addressSpace.copyOutConcretes();

    // mark constant objects as read-only
    for (auto obj : constantObjects)
      obj->setReadOnly(true);
  }
}


bool Executor::branchingPermitted(const ExecutionState &state) const {
  if ((MaxMemoryInhibit && atMemoryLimit) ||
      state.forkDisabled ||
      inhibitForking ||
      (MaxForks!=~0u && stats::forks >= MaxForks)) {

    if (MaxMemoryInhibit && atMemoryLimit)
      klee_warning_once(0, "skipping fork (memory cap exceeded)");
    else if (state.forkDisabled)
      klee_warning_once(0, "skipping fork (fork disabled on current path)");
    else if (inhibitForking)
      klee_warning_once(0, "skipping fork (fork disabled globally)");
    else
      klee_warning_once(0, "skipping fork (max-forks reached)");

    return false;
  }

  return true;
}

void Executor::branch(ExecutionState &state,
                      const std::vector<ref<Expr>> &conditions,
                      std::vector<ExecutionState *> &result,
                      BranchType reason) {
  TimerStatIncrementer timer(stats::forkTime);
  unsigned N = conditions.size();
  assert(N);

  if (!branchingPermitted(state)) {
    unsigned next = theRNG.getInt32() % N;
    for (unsigned i=0; i<N; ++i) {
      if (i == next) {
        result.push_back(&state);
      } else {
        result.push_back(nullptr);
      }
    }
  } else {
    stats::forks += N-1;

    // XXX do proper balance or keep random?
    result.push_back(&state);
    for (unsigned i=1; i<N; ++i) {
      ExecutionState *es = result[theRNG.getInt32() % i];
      ExecutionState *ns = es->branch();
      addedStates.push_back(ns);
      result.push_back(ns);
      processTree->attach(es->ptreeNode, ns, es, reason);
    }
  }

  // If necessary redistribute seeds to match conditions, killing
  // states if necessary due to OnlyReplaySeeds (inefficient but
  // simple).
  
  std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = 
    seedMap.find(&state);
  if (it != seedMap.end()) {
    std::vector<SeedInfo> seeds = it->second;
    seedMap.erase(it);

    // Assume each seed only satisfies one condition (necessarily true
    // when conditions are mutually exclusive and their conjunction is
    // a tautology).
    for (std::vector<SeedInfo>::iterator siit = seeds.begin(), 
           siie = seeds.end(); siit != siie; ++siit) {
      unsigned i;
      for (i=0; i<N; ++i) {
        ref<ConstantExpr> res;
        bool success = solver->getValue(
            state.constraints, siit->assignment.evaluate(conditions[i]), res,
            state.queryMetaData);
        assert(success && "FIXME: Unhandled solver failure");
        (void) success;
        if (res->isTrue())
          break;
      }
      
      // If we didn't find a satisfying condition randomly pick one
      // (the seed will be patched).
      if (i==N)
        i = theRNG.getInt32() % N;

      // Extra check in case we're replaying seeds with a max-fork
      if (result[i])
        seedMap[result[i]].push_back(*siit);
    }

    if (OnlyReplaySeeds) {
      for (unsigned i=0; i<N; ++i) {
        if (result[i] && !seedMap.count(result[i])) {
          terminateStateEarly(*result[i], "Unseeded path during replay", StateTerminationType::Replay);
          result[i] = nullptr;
        }
      }
    }
  }

  for (unsigned i=0; i<N; ++i)
    if (result[i])
      addConstraint(*result[i], conditions[i]);
}

ref<Expr> Executor::maxStaticPctChecks(ExecutionState &current,
                                       ref<Expr> condition) {
  if (isa<klee::ConstantExpr>(condition))
    return condition;

  if (MaxStaticForkPct == 1. && MaxStaticSolvePct == 1. &&
      MaxStaticCPForkPct == 1. && MaxStaticCPSolvePct == 1.)
    return condition;

  // These checks are performed only after at least MaxStaticPctCheckDelay forks
  // have been performed since execution started
  if (stats::forks < MaxStaticPctCheckDelay)
    return condition;

  StatisticManager &sm = *theStatisticManager;
  CallPathNode *cpn = current.stack.back().callPathNode;

  bool reached_max_fork_limit =
      (MaxStaticForkPct < 1. &&
       (sm.getIndexedValue(stats::forks, sm.getIndex()) >
        stats::forks * MaxStaticForkPct));

  bool reached_max_cp_fork_limit = (MaxStaticCPForkPct < 1. && cpn &&
                                    (cpn->statistics.getValue(stats::forks) >
                                     stats::forks * MaxStaticCPForkPct));

  bool reached_max_solver_limit =
      (MaxStaticSolvePct < 1 &&
       (sm.getIndexedValue(stats::solverTime, sm.getIndex()) >
        stats::solverTime * MaxStaticSolvePct));

  bool reached_max_cp_solver_limit =
      (MaxStaticCPForkPct < 1. && cpn &&
       (cpn->statistics.getValue(stats::solverTime) >
        stats::solverTime * MaxStaticCPSolvePct));

  if (reached_max_fork_limit || reached_max_cp_fork_limit ||
      reached_max_solver_limit || reached_max_cp_solver_limit) {
    ref<klee::ConstantExpr> value;
    bool success = solver->getValue(current.constraints, condition, value,
                                    current.queryMetaData);
    assert(success && "FIXME: Unhandled solver failure");
    (void)success;

    std::string msg("skipping fork and concretizing condition (MaxStatic*Pct "
                    "limit reached) at ");
    llvm::raw_string_ostream os(msg);
    os << current.prevPC->getSourceLocation();
    klee_warning_once(0, "%s", os.str().c_str());

    addConstraint(current, EqExpr::create(value, condition));
    condition = value;
  }
  return condition;
}

Executor::StatePair Executor::fork(ExecutionState &current, ref<Expr> condition,
                                   bool isInternal, BranchType reason,
                                   bool useHeapConstraints) {
  Solver::Validity res;
  std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = 
    seedMap.find(&current);
  bool isSeeding = it != seedMap.end();

  if (!isSeeding)
    condition = maxStaticPctChecks(current, condition);

  time::Span timeout = coreSolverTimeout;
  if (isSeeding)
    timeout *= static_cast<unsigned>(it->second.size());
  solver->setTimeout(timeout);

  useHeapConstraints = true;
  bool success;
  if (!CheckBranchBothIntBV) {
    success = solver->evaluate(current.getConstraints(useHeapConstraints),
                               condition, res, current.queryMetaData);
  } else {
    // Check if the true branch is feasible
    bool res_trueBr;
    std::vector<ref<Expr>> unsignedExprs;
    ref<Expr> b2ic = BV2IntExpr::convertConstraint(condition, unsignedExprs);
    ref<Expr> unsignedConstrsTrueBr = current.getUnsignedConstraints(unsignedExprs);
    ref<Expr> condAugTrueBr =
        AndExpr::create(condition, AndExpr::create(b2ic, unsignedConstrsTrueBr));
    ConstraintSet constraints = current.getConstraints(useHeapConstraints);
    std::vector<ref<BV2IntExpr>> tpot_bv2int_exprs;

    success = solver->mayBeTrue(constraints, condAugTrueBr, res_trueBr,
                                current.queryMetaData);

    // Check if the false branch is feasible
    bool res_falseBr;
    // std::vector<ref<Expr>> unsignedExprs;
    b2ic = BV2IntExpr::convertConstraint(NotExpr::create(condition),
                                         unsignedExprs);
    ref<Expr>unsignedConstrsFalseBr = current.getUnsignedConstraints(unsignedExprs);

    ref<Expr> condAugFalseBr = AndExpr::create(
        NotExpr::create(condition), AndExpr::create(b2ic, unsignedConstrsFalseBr));
    success = solver->mayBeTrue(constraints, condAugFalseBr, res_falseBr,
                                current.queryMetaData);

    if (res_trueBr && res_falseBr) {
      res = Solver::Unknown;
    } else if (res_trueBr) {
      res = Solver::True;
      // don't lose unsigned constraints
      addConstraintGuarded(current, unsignedConstrsFalseBr);
    } else if (res_falseBr) {
      res = Solver::False;
      // don't lose unsigned constraints
      addConstraintGuarded(current, unsignedConstrsTrueBr);
    } else {
      assert(false && "Both branches are infeasible");
    }
  }

  solver->setTimeout(time::Span());
  if (!success) {
    current.pc = current.prevPC;
    terminateStateOnSolverError(current, "Query timed out (fork).");
    return StatePair(nullptr, nullptr);
  }

  if (!isSeeding) {
    if (replayPath && !isInternal) {
      assert(replayPosition<replayPath->size() &&
             "ran out of branches in replay path mode");
      bool branch = (*replayPath)[replayPosition++];
      
      if (res==Solver::True) {
        assert(branch && "hit invalid branch in replay path mode");
      } else if (res==Solver::False) {
        assert(!branch && "hit invalid branch in replay path mode");
      } else {
        // add constraints
        if(branch) {
          res = Solver::True;
          addConstraint(current, condition);
        } else  {
          res = Solver::False;
          addConstraint(current, Expr::createIsZero(condition));
        }
      }
    } else if (res==Solver::Unknown) {
      assert(!replayKTest && "in replay mode, only one branch can be true.");
      
      if (!branchingPermitted(current)) {
        TimerStatIncrementer timer(stats::forkTime);
        if (theRNG.getBool()) {
          addConstraint(current, condition);
          res = Solver::True;        
        } else {
          addConstraint(current, Expr::createIsZero(condition));
          res = Solver::False;
        }
      }
    }
  }

  // Fix branch in only-replay-seed mode, if we don't have both true
  // and false seeds.
  if (isSeeding && 
      (current.forkDisabled || OnlyReplaySeeds) && 
      res == Solver::Unknown) {
    bool trueSeed=false, falseSeed=false;
    // Is seed extension still ok here?
    for (std::vector<SeedInfo>::iterator siit = it->second.begin(), 
           siie = it->second.end(); siit != siie; ++siit) {
      ref<ConstantExpr> res;
      bool success = solver->getValue(current.getConstraints(useHeapConstraints),
                                      siit->assignment.evaluate(condition), res,
                                      current.queryMetaData);
      assert(success && "FIXME: Unhandled solver failure");
      (void) success;
      if (res->isTrue()) {
        trueSeed = true;
      } else {
        falseSeed = true;
      }
      if (trueSeed && falseSeed)
        break;
    }
    if (!(trueSeed && falseSeed)) {
      assert(trueSeed || falseSeed);
      
      res = trueSeed ? Solver::True : Solver::False;
      addConstraint(current, trueSeed ? condition : Expr::createIsZero(condition));
    }
  }


  // XXX - even if the constraint is provable one way or the other we
  // can probably benefit by adding this constraint and allowing it to
  // reduce the other constraints. For example, if we do a binary
  // search on a particular value, and then see a comparison against
  // the value it has been fixed at, we should take this as a nice
  // hint to just use the single constraint instead of all the binary
  // search ones. If that makes sense.
  if (res==Solver::True) {
    if (!isInternal) {
      if (pathWriter) {
        current.pathOS << "1";
      }
    }

    return StatePair(&current, nullptr);
  } else if (res==Solver::False) {
    if (!isInternal) {
      if (pathWriter) {
        current.pathOS << "0";
      }
    }

    return StatePair(nullptr, &current);
  } else {
    TimerStatIncrementer timer(stats::forkTime);
    ExecutionState *falseState, *trueState = &current;

    if (!current.lambdaParent) {
      LOG_STEPS_VERBOSE(" ---- Forking ---- ");
    }

    ++stats::forks;

    falseState = trueState->branch();
    addedStates.push_back(falseState);

    if (it != seedMap.end()) {
      std::vector<SeedInfo> seeds = it->second;
      it->second.clear();
      std::vector<SeedInfo> &trueSeeds = seedMap[trueState];
      std::vector<SeedInfo> &falseSeeds = seedMap[falseState];
      for (std::vector<SeedInfo>::iterator siit = seeds.begin(), 
             siie = seeds.end(); siit != siie; ++siit) {
        ref<ConstantExpr> res;
        bool success = solver->getValue(current.constraints,
                                        siit->assignment.evaluate(condition),
                                        res, current.queryMetaData);
        assert(success && "FIXME: Unhandled solver failure");
        (void) success;
        if (res->isTrue()) {
          trueSeeds.push_back(*siit);
        } else {
          falseSeeds.push_back(*siit);
        }
      }
      
      bool swapInfo = false;
      if (trueSeeds.empty()) {
        if (&current == trueState) swapInfo = true;
        seedMap.erase(trueState);
      }
      if (falseSeeds.empty()) {
        if (&current == falseState) swapInfo = true;
        seedMap.erase(falseState);
      }
      if (swapInfo) {
        std::swap(trueState->coveredNew, falseState->coveredNew);
        std::swap(trueState->coveredLines, falseState->coveredLines);
      }
    }

    processTree->attach(current.ptreeNode, falseState, trueState, reason);

    if (pathWriter) {
      // Need to update the pathOS.id field of falseState, otherwise the same id
      // is used for both falseState and trueState.
      falseState->pathOS = pathWriter->open(current.pathOS);
      if (!isInternal) {
        trueState->pathOS << "1";
        falseState->pathOS << "0";
      }
    }
    if (symPathWriter) {
      falseState->symPathOS = symPathWriter->open(current.symPathOS);
      if (!isInternal) {
        trueState->symPathOS << "1";
        falseState->symPathOS << "0";
      }
    }

    addConstraintGuarded(*trueState, condition, true, "fork");
    addConstraintGuarded(*falseState, Expr::createIsZero(condition), true, "fork");

    // Kinda gross, do we even really still want this option?
    if (MaxDepth && MaxDepth<=trueState->depth) {
      terminateStateEarly(*trueState, "max-depth exceeded.", StateTerminationType::MaxDepth);
      terminateStateEarly(*falseState, "max-depth exceeded.", StateTerminationType::MaxDepth);
      return StatePair(nullptr, nullptr);
    }

    return StatePair(trueState, falseState);
  }
}

void Executor::addConstraint(ExecutionState &state, ref<Expr> condition) {
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(condition)) {
    if (!CE->isTrue())
      llvm::report_fatal_error("attempt to add invalid constraint");
    return;
  }

  // Check to see if this constraint violates seeds.
  std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = 
    seedMap.find(&state);
  if (it != seedMap.end()) {
    bool warn = false;
    for (std::vector<SeedInfo>::iterator siit = it->second.begin(), 
           siie = it->second.end(); siit != siie; ++siit) {
      bool res;
      bool success = solver->mustBeFalse(state.constraints,
                                         siit->assignment.evaluate(condition),
                                         res, state.queryMetaData);
      assert(success && "FIXME: Unhandled solver failure");
      (void) success;
      if (res) {
        siit->patchSeed(state, condition, solver);
        warn = true;
      }
    }
    if (warn)
      klee_warning("seeds patched for violating constraint"); 
  }

  state.addConstraint(condition);
  if (ivcEnabled)
    doImpliedValueConcretization(state, condition, 
                                 ConstantExpr::alloc(1, Expr::Bool));
}

ref<Expr> Executor::doTpotSimplifications(ExecutionState &state, ref<Expr> expr) {
  ref<Expr> res = expr;
  res = ConstraintManager::simplifyAddresses(state.constraints, res);
  res = ConstraintManager::simplifyReads(solver->solver.get(), state.constraints, res);
  res = ConstraintManager::instantiteBV2IntAxioms(solver->solver.get(), state.constraints, res);
  return res;
}

bool Executor::addConstraintGuarded(ExecutionState &state, ref<Expr> condition, bool failureIsFatal, std::string annotation) {
  bool res, success;

  condition = doTpotSimplifications(state, condition);

  success = solver->mustBeFalse(
      state.getConstraints(/*useHeapConstraints=*/true), condition, res, state.queryMetaData);
  assert(success && "FIXME: Unhandled solver failure");
  if (res) {
    if (failureIsFatal) {
      terminateStateOnExecError(state, "invalid constraint (provably false)");
    }
    return false;
  } 

  // if condition is over bitvectors, also check that the integer constraints are feasible
  std::vector<ref<Expr>> unsignedExprs;
  ref<Expr> b2ic = BV2IntExpr::convertConstraint(condition, unsignedExprs);
  ref<Expr> unsignedConstrs = state.getUnsignedConstraints(unsignedExprs);
  b2ic = AndExpr::create(b2ic, unsignedConstrs);
  b2ic = doTpotSimplifications(state, b2ic);

  success = solver->mustBeFalse(
      state.getConstraints(/*useHeapConstraints=*/true), b2ic, res, state.queryMetaData);
  assert(success && "FIXME: Unhandled solver failure");
  if (res) {
    if (failureIsFatal) {
      terminateStateOnExecError(state, "invalid constraint (provably false)");
    }
    return false;
  }
  // condition = AndExpr::create(condition, unsignedConstrs);


  condition->skipBV2Int = true; // we have already converted (and optimized) the constraint.
  condition = AndExpr::create(condition, b2ic);
  // condition = doTpotSimplifications(state, condition);

  if (AnnotateSMT) {
    if (!annotation.empty()) {
      annotation = "(" + annotation + ") ";
    }
    std::string annotStr = "---- " + annotation + \
      state.prevPC->getSourceLocation() + ": " + std::to_string(state.prevPC->info->assemblyLine) \
      + " ----";

    ref<Expr> annotExpr = EqExpr::create(BitVecExpr::create(annotStr, 2), ConstantExpr::alloc(0, 2));
    condition = AndExpr::create(annotExpr, condition);
  }

  addConstraint(state, condition);
  return true;
}

const Cell& Executor::eval(KInstruction *ki, unsigned index, 
                           ExecutionState &state) const {
  assert(index < ki->inst->getNumOperands());
  int vnumber = ki->operands[index];

  assert(vnumber != -1 &&
         "Invalid operand to eval(), not a value or constant!");

  // Determine if this is a constant or not.
  if (vnumber < 0) {
    unsigned index = -vnumber - 2;
    return kmodule->constantTable[index];
  } else {
    unsigned index = vnumber;
    StackFrame &sf = state.stack.back();
    return sf.locals[index];
  }
}

void Executor::bindLocal(KInstruction *target, ExecutionState &state, 
                         ref<Expr> value) {
  getDestCell(state, target).value = value;
}

void Executor::bindArgument(KFunction *kf, unsigned index, 
                            ExecutionState &state, ref<Expr> value) {
  getArgumentCell(state, kf, index).value = value;
}

ref<Expr> Executor::toUnique(const ExecutionState &state, 
                             ref<Expr> &e) {
  ref<Expr> result = e;

  if (!isa<ConstantExpr>(e)) {
    ref<ConstantExpr> value;
    bool isTrue = false;
    e = optimizer.optimizeExpr(e, true);
    solver->setTimeout(coreSolverTimeout);
    if (solver->getValue(state.constraints, e, value, state.queryMetaData)) {
      ref<Expr> cond = EqExpr::create(e, value);
      cond = optimizer.optimizeExpr(cond, false);
      if (solver->mustBeTrue(state.constraints, cond, isTrue,
                             state.queryMetaData) &&
          isTrue)
        result = value;
    }
    solver->setTimeout(time::Span());
  }
  
  return result;
}


/* Concretize the given expression, and return a possible constant value. 
   'reason' is just a documentation string stating the reason for concretization. */
ref<klee::ConstantExpr> 
Executor::toConstant(ExecutionState &state, 
                     ref<Expr> e,
                     const char *reason) {
  e = ConstraintManager::simplifyExpr(state.constraints, e);
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(e))
    return CE;

  ref<ConstantExpr> value;
  bool success =
      solver->getValue(state.constraints, e, value, state.queryMetaData);
  assert(success && "FIXME: Unhandled solver failure");
  (void) success;

  std::string str;
  llvm::raw_string_ostream os(str);
  os << "silently concretizing (reason: " << reason << ") expression " << e
     << " to value " << value << " (" << (*(state.pc)).info->file << ":"
     << (*(state.pc)).info->line << ")";

  if (AllExternalWarnings)
    klee_warning("%s", os.str().c_str());
  else
    klee_warning_once(reason, "%s", os.str().c_str());

  addConstraintGuarded(state, EqExpr::create(e, value));
    
  return value;
}

void Executor::executeGetValue(ExecutionState &state,
                               ref<Expr> e,
                               KInstruction *target) {
  e = ConstraintManager::simplifyExpr(state.constraints, e);
  std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = 
    seedMap.find(&state);
  if (it==seedMap.end() || isa<ConstantExpr>(e)) {
    ref<ConstantExpr> value;
    e = optimizer.optimizeExpr(e, true);
    bool success =
        solver->getValue(state.constraints, e, value, state.queryMetaData);
    assert(success && "FIXME: Unhandled solver failure");
    (void) success;
    bindLocal(target, state, value);
  } else {
    std::set< ref<Expr> > values;
    for (std::vector<SeedInfo>::iterator siit = it->second.begin(), 
           siie = it->second.end(); siit != siie; ++siit) {
      ref<Expr> cond = siit->assignment.evaluate(e);
      cond = optimizer.optimizeExpr(cond, true);
      ref<ConstantExpr> value;
      bool success =
          solver->getValue(state.constraints, cond, value, state.queryMetaData);
      assert(success && "FIXME: Unhandled solver failure");
      (void) success;
      values.insert(value);
    }
    
    std::vector< ref<Expr> > conditions;
    for (std::set< ref<Expr> >::iterator vit = values.begin(), 
           vie = values.end(); vit != vie; ++vit)
      conditions.push_back(EqExpr::create(e, *vit));

    std::vector<ExecutionState*> branches;
    branch(state, conditions, branches, BranchType::GetVal);
    
    std::vector<ExecutionState*>::iterator bit = branches.begin();
    for (std::set< ref<Expr> >::iterator vit = values.begin(), 
           vie = values.end(); vit != vie; ++vit) {
      ExecutionState *es = *bit;
      if (es)
        bindLocal(target, *es, *vit);
      ++bit;
    }
  }
}

void Executor::printDebugInstructions(ExecutionState &state) {
  // print nothing if option unset
  if (DebugPrintInstructions.getBits() == 0)
    return;

  // set output stream (stderr/file)
  llvm::raw_ostream *stream = nullptr;
  if (DebugPrintInstructions.isSet(STDERR_ALL) ||
      DebugPrintInstructions.isSet(STDERR_SRC) ||
      DebugPrintInstructions.isSet(STDERR_COMPACT))
    stream = &llvm::errs();
  else
    stream = &debugLogBuffer;

  // print:
  //   [all]     src location:asm line:state ID:instruction
  //   [compact]              asm line:state ID
  //   [src]     src location:asm line:state ID
  if (!DebugPrintInstructions.isSet(STDERR_COMPACT) &&
      !DebugPrintInstructions.isSet(FILE_COMPACT)) {
    (*stream) << "     " << state.pc->getSourceLocation() << ':';
  }

  (*stream) << state.pc->info->assemblyLine << ':' << state.getID();

  if (DebugPrintInstructions.isSet(STDERR_ALL) ||
      DebugPrintInstructions.isSet(FILE_ALL))
    (*stream) << ':' << *(state.pc->inst);

  (*stream) << '\n';

  // flush to file
  if (DebugPrintInstructions.isSet(FILE_ALL) ||
      DebugPrintInstructions.isSet(FILE_COMPACT) ||
      DebugPrintInstructions.isSet(FILE_SRC)) {
    debugLogBuffer.flush();
    (*debugInstFile) << debugLogBuffer.str();
    debugBufferString = "";
  }
}

void Executor::stepInstruction(ExecutionState &state) {
  printDebugInstructions(state);

  if (EnableFailingCodePath) state.instHistory.push_back(state.pc);

  if (statsTracker)
    statsTracker->stepInstruction(state);

  ++stats::instructions;
  ++state.steppedInstructions;
  state.prevPC = state.pc;
  ++state.pc;

  if (stats::instructions == MaxInstructions)
    haltExecution = true;
}

static inline const llvm::fltSemantics *fpWidthToSemantics(unsigned width) {
  switch (width) {
  case Expr::Int32:
    return &llvm::APFloat::IEEEsingle();
  case Expr::Int64:
    return &llvm::APFloat::IEEEdouble();
  case Expr::Fl80:
    return &llvm::APFloat::x87DoubleExtended();
  default:
    return 0;
  }
}

MemoryObject *Executor::serializeLandingpad(ExecutionState &state,
                                            const llvm::LandingPadInst &lpi,
                                            bool &stateTerminated) {
  stateTerminated = false;

  std::vector<unsigned char> serialized;

  for (unsigned current_clause_id = 0; current_clause_id < lpi.getNumClauses();
       ++current_clause_id) {
    llvm::Constant *current_clause = lpi.getClause(current_clause_id);
    if (lpi.isCatch(current_clause_id)) {
      // catch-clause
      serialized.push_back(0);

      std::uint64_t ti_addr = 0;

      llvm::BitCastOperator *clause_bitcast =
          dyn_cast<llvm::BitCastOperator>(current_clause);
      if (clause_bitcast) {
        llvm::GlobalValue *clause_type =
            dyn_cast<GlobalValue>(clause_bitcast->getOperand(0));

        ti_addr = globalAddresses[clause_type]->getZExtValue();
      } else if (current_clause->isNullValue()) {
        ti_addr = 0;
      } else {
        terminateStateOnExecError(
            state, "Internal: Clause is not a bitcast or null (catch-all)");
        stateTerminated = true;
        return nullptr;
      }
      const std::size_t old_size = serialized.size();
      serialized.resize(old_size + 8);
      memcpy(serialized.data() + old_size, &ti_addr, sizeof(ti_addr));
    } else if (lpi.isFilter(current_clause_id)) {
      if (current_clause->isNullValue()) {
        // special handling for a catch-all filter clause, i.e., "[0 x i8*]"
        // for this case we serialize 1 element..
        serialized.push_back(1);
        // which is a 64bit-wide 0.
        serialized.resize(serialized.size() + 8, 0);
      } else {
        llvm::ConstantArray const *ca =
            cast<llvm::ConstantArray>(current_clause);

        // serialize `num_elements+1` as unsigned char
        unsigned const num_elements = ca->getNumOperands();
        unsigned char serialized_num_elements = 0;

        if (num_elements >=
            std::numeric_limits<decltype(serialized_num_elements)>::max()) {
          terminateStateOnExecError(
              state, "Internal: too many elements in landingpad filter");
          stateTerminated = true;
          return nullptr;
        }

        serialized_num_elements = num_elements;
        serialized.push_back(serialized_num_elements + 1);

        // serialize the exception-types occurring in this filter-clause
        for (llvm::Value const *v : ca->operands()) {
          llvm::BitCastOperator const *bitcast =
              dyn_cast<llvm::BitCastOperator>(v);
          if (!bitcast) {
            terminateStateOnExecError(state,
                                      "Internal: expected value inside a "
                                      "filter-clause to be a bitcast");
            stateTerminated = true;
            return nullptr;
          }

          llvm::GlobalValue const *clause_value =
              dyn_cast<GlobalValue>(bitcast->getOperand(0));
          if (!clause_value) {
            terminateStateOnExecError(state,
                                      "Internal: expected value inside a "
                                      "filter-clause bitcast to be a GlobalValue");
            stateTerminated = true;
            return nullptr;
          }

          std::uint64_t const ti_addr =
              globalAddresses[clause_value]->getZExtValue();

          const std::size_t old_size = serialized.size();
          serialized.resize(old_size + 8);
          memcpy(serialized.data() + old_size, &ti_addr, sizeof(ti_addr));
        }
      }
    }
  }

  MemoryObject *mo =
      memory->allocate(serialized.size(), true, false, nullptr, 1);
  ObjectState *os = bindObjectInState(state, mo, false);
  for (unsigned i = 0; i < serialized.size(); i++) {
    os->write8(i, serialized[i]);
  }

  return mo;
}

void Executor::unwindToNextLandingpad(ExecutionState &state) {
  UnwindingInformation *ui = state.unwindingInformation.get();
  assert(ui && "unwinding without unwinding information");

  std::size_t startIndex;
  std::size_t lowestStackIndex;
  bool popFrames;

  if (auto *sui = dyn_cast<SearchPhaseUnwindingInformation>(ui)) {
    startIndex = sui->unwindingProgress;
    lowestStackIndex = 0;
    popFrames = false;
  } else if (auto *cui = dyn_cast<CleanupPhaseUnwindingInformation>(ui)) {
    startIndex = state.stack.size() - 1;
    lowestStackIndex = cui->catchingStackIndex;
    popFrames = true;
  } else {
    assert(false && "invalid UnwindingInformation subclass");
  }

  for (std::size_t i = startIndex; i > lowestStackIndex; i--) {
    auto const &sf = state.stack.at(i);

    Instruction *inst = sf.caller ? sf.caller->inst : nullptr;

    if (popFrames) {
      state.popFrame();
      if (statsTracker != nullptr) {
        statsTracker->framePopped(state);
      }
    }

    if (InvokeInst *invoke = dyn_cast<InvokeInst>(inst)) {
      // we found the next invoke instruction in the call stack, handle it
      // depending on the current phase.
      if (auto *sui = dyn_cast<SearchPhaseUnwindingInformation>(ui)) {
        // in the search phase, run personality function to check if this
        // landingpad catches the exception

        LandingPadInst *lpi = invoke->getUnwindDest()->getLandingPadInst();
        assert(lpi && "unwind target of an invoke instruction did not lead to "
                      "a landingpad");

        // check if this is a pure cleanup landingpad first
        if (lpi->isCleanup() && lpi->getNumClauses() == 0) {
          // pure cleanup lpi, this can't be a handler, so skip it
          continue;
        }

        bool stateTerminated = false;
        MemoryObject *clauses_mo =
            serializeLandingpad(state, *lpi, stateTerminated);
        assert((stateTerminated != bool(clauses_mo)) &&
               "illegal serializeLandingpad result");

        if (stateTerminated) {
          return;
        }

        assert(sui->serializedLandingpad == nullptr &&
               "serializedLandingpad should be reset");
        sui->serializedLandingpad = clauses_mo;

        llvm::Function *personality_fn =
            kmodule->module->getFunction("_klee_eh_cxx_personality");
        KFunction *kf = kmodule->functionMap[personality_fn];

        state.pushFrame(state.prevPC, kf);
        state.pc = kf->instructions;
        bindArgument(kf, 0, state, sui->exceptionObject);
        bindArgument(kf, 1, state, clauses_mo->getSizeExpr());
        bindArgument(kf, 2, state, clauses_mo->getBaseExpr());

        if (statsTracker) {
          statsTracker->framePushed(state,
                                    &state.stack[state.stack.size() - 2]);
        }

        // make sure we remember our search progress afterwards
        sui->unwindingProgress = i - 1;
      } else {
        // in the cleanup phase, redirect control flow
        transferToBasicBlock(invoke->getUnwindDest(), invoke->getParent(),
                             state);
      }

      // we are done, stop search/unwinding here
      return;
    }
  }

  // no further invoke instruction/landingpad found
  if (isa<SearchPhaseUnwindingInformation>(ui)) {
    // in phase 1, simply stop unwinding. this will return
    // control flow back to _Unwind_RaiseException, which will
    // return the correct error.

    // clean up unwinding state
    state.unwindingInformation.reset();
  } else {
    // in phase 2, this represent a situation that should
    // not happen, as we only progressed to phase 2 because
    // we found a handler in phase 1.
    // therefore terminate the state.
    terminateStateOnExecError(state,
                              "Missing landingpad in phase 2 of unwinding");
  }
}

ref<klee::ConstantExpr> Executor::getEhTypeidFor(ref<Expr> type_info) {
  // FIXME: Handling getEhTypeidFor is non-deterministic and depends on the
  //        order states have been processed and executed.
  auto eh_type_iterator =
      std::find(std::begin(eh_typeids), std::end(eh_typeids), type_info);
  if (eh_type_iterator == std::end(eh_typeids)) {
    eh_typeids.push_back(type_info);
    eh_type_iterator = std::prev(std::end(eh_typeids));
  }
  // +1 because typeids must always be positive, so they can be distinguished
  // from 'no landingpad clause matched' which has value 0
  auto res = ConstantExpr::create(eh_type_iterator - std::begin(eh_typeids) + 1,
                                  Expr::Int32);
  return res;
}

void Executor::executeCall(ExecutionState &state, KInstruction *ki, Function *f,
                           std::vector<ref<Expr>> &arguments) {
  Instruction *i = ki->inst;
  //! These are already flagged in executeInstruction
  //! TPot removes this check so that lamdas are not potentially ignored.
  // if (isa_and_nonnull<DbgInfoIntrinsic>(i))
  //   return;
  if (f && f->isDeclaration()) {
    switch (f->getIntrinsicID()) {
    case Intrinsic::not_intrinsic:
      // state may be destroyed by this call, cannot touch
      callExternalFunction(state, ki, f, arguments);
      break;
    case Intrinsic::fabs: {
      ref<ConstantExpr> arg =
          toConstant(state, arguments[0], "floating point");
      if (!fpWidthToSemantics(arg->getWidth()))
        return terminateStateOnExecError(
            state, "Unsupported intrinsic llvm.fabs call");

      llvm::APFloat Res(*fpWidthToSemantics(arg->getWidth()),
                        arg->getAPValue());
      Res = llvm::abs(Res);

      bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
      break;
    }

#if LLVM_VERSION_CODE >= LLVM_VERSION(12, 0)
    case Intrinsic::abs: {
      if (isa<VectorType>(i->getOperand(0)->getType()))
        return terminateStateOnExecError(
            state, "llvm.abs with vectors is not supported");

      ref<Expr> op = eval(ki, 1, state).value;
      ref<Expr> poison = eval(ki, 2, state).value;

      assert(poison->getWidth() == 1 && "Second argument is not an i1");
      unsigned bw = op->getWidth();

      uint64_t moneVal = APInt(bw, -1, true).getZExtValue();
      uint64_t sminVal = APInt::getSignedMinValue(bw).getZExtValue();

      ref<ConstantExpr> zero = ConstantExpr::create(0, bw);
      ref<ConstantExpr> mone = ConstantExpr::create(moneVal, bw);
      ref<ConstantExpr> smin = ConstantExpr::create(sminVal, bw);

      if (poison->isTrue()) {
        ref<Expr> issmin = EqExpr::create(op, smin);
        if (issmin->isTrue())
          return terminateStateOnExecError(
              state, "llvm.abs called with poison and INT_MIN");
      }

      // conditions to flip the sign: INT_MIN < op < 0
      ref<Expr> negative = SltExpr::create(op, zero);
      ref<Expr> notsmin = NeExpr::create(op, smin);
      ref<Expr> cond = AndExpr::create(negative, notsmin);

      // flip and select the result
      ref<Expr> flip = MulExpr::create(op, mone);
      ref<Expr> result = SelectExpr::create(cond, flip, op);

      bindLocal(ki, state, result);
      break;
    }

    case Intrinsic::smax:
    case Intrinsic::smin:
    case Intrinsic::umax:
    case Intrinsic::umin: {
      if (isa<VectorType>(i->getOperand(0)->getType()) ||
          isa<VectorType>(i->getOperand(1)->getType()))
        return terminateStateOnExecError(
            state, "llvm.{s,u}{max,min} with vectors is not supported");

      ref<Expr> op1 = eval(ki, 1, state).value;
      ref<Expr> op2 = eval(ki, 2, state).value;

      ref<Expr> cond = nullptr;
      if (f->getIntrinsicID() == Intrinsic::smax)
        cond = SgtExpr::create(op1, op2);
      else if (f->getIntrinsicID() == Intrinsic::smin)
        cond = SltExpr::create(op1, op2);
      else if (f->getIntrinsicID() == Intrinsic::umax)
        cond = UgtExpr::create(op1, op2);
      else // (f->getIntrinsicID() == Intrinsic::umin)
        cond = UltExpr::create(op1, op2);

      ref<Expr> result = SelectExpr::create(cond, op1, op2);
      bindLocal(ki, state, result);
      break;
    }
#endif

#if LLVM_VERSION_CODE >= LLVM_VERSION(7, 0)
    case Intrinsic::fshr:
    case Intrinsic::fshl: {
      ref<Expr> op1 = eval(ki, 1, state).value;
      ref<Expr> op2 = eval(ki, 2, state).value;
      ref<Expr> op3 = eval(ki, 3, state).value;
      unsigned w = op1->getWidth();
      assert(w == op2->getWidth() && "type mismatch");
      assert(w == op3->getWidth() && "type mismatch");
      ref<Expr> c = ConcatExpr::create(op1, op2);
      // op3 = zeroExtend(op3 % w)
      op3 = URemExpr::create(op3, ConstantExpr::create(w, w));
      op3 = ZExtExpr::create(op3, w+w);
      if (f->getIntrinsicID() == Intrinsic::fshl) {
        // shift left and take top half
        ref<Expr> s = ShlExpr::create(c, op3);
        bindLocal(ki, state, ExtractExpr::create(s, w, w));
      } else {
        // shift right and take bottom half
        // note that LShr and AShr will have same behaviour
        ref<Expr> s = LShrExpr::create(c, op3);
        bindLocal(ki, state, ExtractExpr::create(s, 0, w));
      }
      break;
    }
#endif

    // va_arg is handled by caller and intrinsic lowering, see comment for
    // ExecutionState::varargs
    case Intrinsic::vastart: {
      StackFrame &sf = state.stack.back();

      // varargs can be zero if no varargs were provided
      if (!sf.varargs)
        return;

      // FIXME: This is really specific to the architecture, not the pointer
      // size. This happens to work for x86-32 and x86-64, however.
      Expr::Width WordSize = Context::get().getPointerWidth();
      if (WordSize == Expr::Int32) {
        executeMemoryOperation(state, MEMOP_WRITE, arguments[0],
                               sf.varargs->getBaseExpr(), 0, 0, "");
      } else {
        assert(WordSize == Expr::Int64 && "Unknown word size!");

        // x86-64 has quite complicated calling convention. However,
        // instead of implementing it, we can do a simple hack: just
        // make a function believe that all varargs are on stack.
        executeMemoryOperation(
            state, MEMOP_WRITE, 
            arguments[0],
            ConstantExpr::create(48, 32), 0, 0, ""); // gp_offset
        executeMemoryOperation(
            state, MEMOP_WRITE,
            AddExpr::create(arguments[0], ConstantExpr::create(4, 64)),
            ConstantExpr::create(304, 32), 0, 0, ""); // fp_offset
        executeMemoryOperation(
            state, MEMOP_WRITE,
            AddExpr::create(arguments[0], ConstantExpr::create(8, 64)),
            sf.varargs->getBaseExpr(), 0, 0, ""); // overflow_arg_area
        executeMemoryOperation(
            state, MEMOP_WRITE,
            AddExpr::create(arguments[0], ConstantExpr::create(16, 64)),
            ConstantExpr::create(0, 64), 0, 0, ""); // reg_save_area
      }
      break;
    }

#ifdef SUPPORT_KLEE_EH_CXX
    case Intrinsic::eh_typeid_for: {
      bindLocal(ki, state, getEhTypeidFor(arguments.at(0)));
      break;
    }
#endif

    case Intrinsic::vaend:
      // va_end is a noop for the interpreter.
      //
      // FIXME: We should validate that the target didn't do something bad
      // with va_end, however (like call it twice).
      break;

    case Intrinsic::vacopy:
      // va_copy should have been lowered.
      //
      // FIXME: It would be nice to check for errors in the usage of this as
      // well.
    default:
      klee_warning("unimplemented intrinsic: %s", f->getName().data());
      terminateStateOnExecError(state, "unimplemented intrinsic");
      return;
    }

    if (InvokeInst *ii = dyn_cast<InvokeInst>(i)) {
      transferToBasicBlock(ii->getNormalDest(), i->getParent(), state);
    }
  } else {
    // Check if maximum stack size was reached.
    // We currently only count the number of stack frames
    if (RuntimeMaxStackFrames && state.stack.size() > RuntimeMaxStackFrames) {
      terminateStateEarly(state, "Maximum stack size reached.", StateTerminationType::OutOfStackMemory);
      klee_warning("Maximum stack size reached.");
      return;
    }

    // FIXME: I'm not really happy about this reliance on prevPC but it is ok, I
    // guess. This just done to avoid having to pass KInstIterator everywhere
    // instead of the actual instruction, since we can't make a KInstIterator
    // from just an instruction (unlike LLVM).
    KFunction *kf = kmodule->functionMap[f];

    state.pushFrame(state.prevPC, kf);
    state.pc = kf->instructions;

    if (statsTracker)
      statsTracker->framePushed(state, &state.stack[state.stack.size() - 2]);

    // TODO: support zeroext, signext, sret attributes

    unsigned callingArgs = arguments.size();
    unsigned funcArgs = f->arg_size();
    if (!f->isVarArg()) {
      if (callingArgs > funcArgs) {
        klee_warning_once(f, "calling %s with extra arguments.",
                          f->getName().data());
      } else if (callingArgs < funcArgs) {
        terminateStateOnUserError(state, "calling function with too few arguments");
        return;
      }
    } else {
      if (callingArgs < funcArgs) {
        terminateStateOnUserError(state, "calling function with too few arguments");
        return;
      }

      // Only x86-32 and x86-64 are supported
      Expr::Width WordSize = Context::get().getPointerWidth();
      assert(((WordSize == Expr::Int32) || (WordSize == Expr::Int64)) &&
             "Unknown word size!");

      uint64_t size = 0; // total size of variadic arguments
      bool requires16ByteAlignment = false;

      uint64_t offsets[callingArgs]; // offsets of variadic arguments
      uint64_t argWidth;             // width of current variadic argument

#if LLVM_VERSION_CODE >= LLVM_VERSION(8, 0)
      const CallBase &cs = cast<CallBase>(*i);
#else
      const CallSite cs(i);
#endif
      for (unsigned k = funcArgs; k < callingArgs; k++) {
        if (cs.isByValArgument(k)) {
#if LLVM_VERSION_CODE >= LLVM_VERSION(9, 0)
          Type *t = cs.getParamByValType(k);
#else
          auto arg = cs.getArgOperand(k);
          Type *t = arg->getType();
          assert(t->isPointerTy());
          t = t->getPointerElementType();
#endif
          argWidth = kmodule->targetData->getTypeSizeInBits(t);
        } else {
          argWidth = arguments[k]->getWidth();
        }

        if (WordSize == Expr::Int32) {
          offsets[k] = size;
          size += Expr::getMinBytesForWidth(argWidth);
        } else {
#if LLVM_VERSION_CODE >= LLVM_VERSION(11, 0)
          MaybeAlign ma = cs.getParamAlign(k);
          unsigned alignment = ma ? ma->value() : 0;
#else
          unsigned alignment = cs.getParamAlignment(k);
#endif

          // AMD64-ABI 3.5.7p5: Step 7. Align l->overflow_arg_area upwards to a
          // 16 byte boundary if alignment needed by type exceeds 8 byte
          // boundary.
          if (!alignment && argWidth > Expr::Int64) {
            alignment = 16;
            requires16ByteAlignment = true;
          }

          if (!alignment)
            alignment = 8;

          size = llvm::alignTo(size, alignment);
          offsets[k] = size;

          // AMD64-ABI 3.5.7p5: Step 9. Set l->overflow_arg_area to:
          // l->overflow_arg_area + sizeof(type)
          // Step 10. Align l->overflow_arg_area upwards to an 8 byte boundary.
          size += llvm::alignTo(argWidth, WordSize) / 8;
        }
      }

      StackFrame &sf = state.stack.back();
      MemoryObject *mo = sf.varargs =
          memory->allocate(size, true, false, state.prevPC->inst,
                           (requires16ByteAlignment ? 16 : 8));
      if (!mo && size) {
        terminateStateOnExecError(state, "out of memory (varargs)");
        return;
      }

      if (mo) {
        if ((WordSize == Expr::Int64) && (mo->address & 15) &&
            requires16ByteAlignment) {
          // Both 64bit Linux/Glibc and 64bit MacOSX should align to 16 bytes.
          klee_warning_once(
              0, "While allocating varargs: malloc did not align to 16 bytes.");
        }

        ObjectState *os = bindObjectInState(state, mo, true);

        for (unsigned k = funcArgs; k < callingArgs; k++) {
          if (!cs.isByValArgument(k)) {
            os->write(offsets[k], arguments[k]);
          } else {
            ConstantExpr *CE = dyn_cast<ConstantExpr>(arguments[k]);
            assert(CE); // byval argument needs to be a concrete pointer

            ObjectPair op;
            state.addressSpace.resolveOne(CE, op);
            const ObjectState *osarg = op.second;
            assert(osarg);
            for (unsigned i = 0; i < osarg->size; i++)
              os->write(offsets[k] + i, osarg->read8(i, false));
          }
        }
      }
    }

    unsigned numFormals = f->arg_size();
    for (unsigned k = 0; k < numFormals; k++)
      bindArgument(kf, k, state, arguments[k]);
  }
}

void Executor::transferToBasicBlock(BasicBlock *dst, BasicBlock *src, 
                                    ExecutionState &state) {
  // Note that in general phi nodes can reuse phi values from the same
  // block but the incoming value is the eval() result *before* the
  // execution of any phi nodes. this is pathological and doesn't
  // really seem to occur, but just in case we run the PhiCleanerPass
  // which makes sure this cannot happen and so it is safe to just
  // eval things in order. The PhiCleanerPass also makes sure that all
  // incoming blocks have the same order for each PHINode so we only
  // have to compute the index once.
  //
  // With that done we simply set an index in the state so that PHI
  // instructions know which argument to eval, set the pc, and continue.
  
  // XXX this lookup has to go ?
  KFunction *kf = state.stack.back().kf;
  unsigned entry = kf->basicBlockEntry[dst];
  state.pc = &kf->instructions[entry];
  if (state.pc->inst->getOpcode() == Instruction::PHI) {
    PHINode *first = static_cast<PHINode*>(state.pc->inst);
    state.incomingBBIndex = first->getBasicBlockIndex(src);
  }
}

/// Compute the true target of a function call, resolving LLVM aliases
/// and bitcasts.
Function* Executor::getTargetFunction(Value *calledVal, ExecutionState &state) {
  SmallPtrSet<const GlobalValue*, 3> Visited;

  Constant *c = dyn_cast<Constant>(calledVal);
  if (!c)
    return 0;

  while (true) {
    if (GlobalValue *gv = dyn_cast<GlobalValue>(c)) {
      if (!Visited.insert(gv).second)
        return 0;

      if (Function *f = dyn_cast<Function>(gv))
        return f;
      else if (GlobalAlias *ga = dyn_cast<GlobalAlias>(gv))
        c = ga->getAliasee();
      else
        return 0;
    } else if (llvm::ConstantExpr *ce = dyn_cast<llvm::ConstantExpr>(c)) {
      if (ce->getOpcode()==Instruction::BitCast)
        c = ce->getOperand(0);
      else
        return 0;
    } else
      return 0;
  }
}

void Executor::trySolveVariableInSmokeTest(
    ExecutionState &state, std::vector<std::string> &failedVariables,
    bool &hasSuccess, ExecutionState *&eq_state,
    const std::pair<const MemoryObject *, ref<ObjectState>> &entry) {
  if (entry.first->name == "unnamed")
    return;
  // klee_message("\033[31m address: %ld\033[0m", entry.first->address);
  // klee_message("\033[31m name: %s\033[0m", entry.first->name.c_str());
  if (!entry.second->forceFlushToConcreteStore(solver, *eq_state)) {
    failedVariables.push_back(entry.first->name);
  } else {
    hasSuccess = true;
    ref<Expr> x = entry.second->read(0, entry.second->size * 8, false);
    // x->dump();
    uint64_t value = 0ull;
    for (unsigned offset = 0; offset < entry.second->size; offset++) {
      // klee_message("0x%x", entry.second->getConcrete(offset));
      uint64_t tmp = entry.second->getConcrete(offset);
      value += tmp << (offset * 8);
      // klee_message("value: 0x%32lx", value);
    }
    // klee_message("value: 0x%lx", value);
    ref<Expr> valueExpr = ConstantExpr::create(value, entry.second->size * 8);
    ref<Expr> eq = EqExpr::create(x, valueExpr);

    eq = ConstraintManager::simplifyExpr(eq_state->constraints, eq);
    if (eq->isFalse()) {
      // TODO: I do not know why this happens
      return;
    }
    // dump all constraints
    // klee_message("\033[31m constraints for %s:\033[0m", entry.first->name.c_str());
    // for (auto constraint : eq_state->constraints) {
    //   constraint->dump();
    // }

    eq_state->addConstraint(eq);

    // klee_message("\033[31m constraints for %s after add the eq constraint:\033[0m", entry.first->name.c_str());
    // for (auto constraint : eq_state->constraints) {
    //   constraint->dump();
    // }

    ref<Expr> ne = NeExpr::create(x, valueExpr);
    state.addConstraint(ne);

    // for (unsigned offset = 0; offset < entry.second->size; offset++) {
    //   klee_message("value: %0x", entry.second->getConcrete(offset));
    //   ref<Expr> x = entry.second->read8(offset);
    //   ref<Expr> value =
    //       ConstantExpr::create(entry.second->getConcrete(offset), Expr::Int8);
    //   ref<Expr> eq = EqExpr::create(x, value);
    //   eq_state->addConstraint(eq);
    //   // os->write8(offset, entry.second->getConcrete(offset));

    //   ref<Expr> ne = NeExpr::create(x, value);
    //   state.addConstraint(ne);
    // }
  }
}

void Executor::executeInstruction(ExecutionState &state, KInstruction *ki) {
  Instruction *i = ki->inst;
  switch (i->getOpcode()) {
    // Control flow
  case Instruction::Ret: {
    ReturnInst *ri = cast<ReturnInst>(i);
    KInstIterator kcaller = state.stack.back().caller;
    Instruction *caller = kcaller ? kcaller->inst : nullptr;
    bool isVoidReturn = (ri->getNumOperands() == 0);
    ref<Expr> result = ConstantExpr::alloc(0, Expr::Bool);
    
    if (!isVoidReturn) {
      result = eval(ki, 0, state).value;
    }

    // If returning from an API function, reset all names
    if (tpotAPIFunctions.find(ri->getFunction()) != tpotAPIFunctions.end()) {
      assert(!state.heap.has_unnamed_shortcut && "multiple API funcs. has_unnnames_shortcut won't work.");
      state.heap.has_unnamed_shortcut = true;
    }
    
    if (state.stack.size() <= 1) {
      assert(!caller && "caller set on initial stack frame");
      tpot_message("Terminating state");
      terminateStateOnExit(state, result);
    } else {
      state.popFrame();

      if (statsTracker)
        statsTracker->framePopped(state);

      if (InvokeInst *ii = dyn_cast<InvokeInst>(caller)) {
        transferToBasicBlock(ii->getNormalDest(), caller->getParent(), state);
      } else {
        state.pc = kcaller;
        ++state.pc;
      }

#ifdef SUPPORT_KLEE_EH_CXX
      if (ri->getFunction()->getName() == "_klee_eh_cxx_personality") {
        assert(dyn_cast<ConstantExpr>(result) &&
               "result from personality fn must be a concrete value");

        auto *sui = dyn_cast_or_null<SearchPhaseUnwindingInformation>(
            state.unwindingInformation.get());
        assert(sui && "return from personality function outside of "
                      "search phase unwinding");

        // unbind the MO we used to pass the serialized landingpad
        state.addressSpace.unbindObject(sui->serializedLandingpad);
        sui->serializedLandingpad = nullptr;

        if (result->isZero()) {
          // this lpi doesn't handle the exception, continue the search
          unwindToNextLandingpad(state);
        } else {
          // a clause (or a catch-all clause or filter clause) matches:
          // remember the stack index and switch to cleanup phase
          state.unwindingInformation =
              std::make_unique<CleanupPhaseUnwindingInformation>(
                  sui->exceptionObject, cast<ConstantExpr>(result),
                  sui->unwindingProgress);
          // this pointer is now invalidated
          sui = nullptr;
          // continue the unwinding process (which will now start with the
          // cleanup phase)
          unwindToNextLandingpad(state);
        }

        // never return normally from the personality fn
        break;
      }
#endif // SUPPORT_KLEE_EH_CXX

      if (!isVoidReturn) {
        Type *t = caller->getType();
        if (t != Type::getVoidTy(i->getContext())) {
          // may need to do coercion due to bitcasts
          Expr::Width from = result->getWidth();
          Expr::Width to = getWidthForLLVMType(t);
            
          if (from != to) {
#if LLVM_VERSION_CODE >= LLVM_VERSION(8, 0)
            const CallBase &cs = cast<CallBase>(*caller);
#else
            const CallSite cs(isa<InvokeInst>(caller)
                                  ? CallSite(cast<InvokeInst>(caller))
                                  : CallSite(cast<CallInst>(caller)));
#endif

            // XXX need to check other param attrs ?
            bool isSExt = cs.hasRetAttr(llvm::Attribute::SExt);
            if (isSExt) {
              result = SExtExpr::create(result, to);
            } else {
              result = ZExtExpr::create(result, to);
            }
          }

          bindLocal(kcaller, state, result);
        }
      } else {
        // We check that the return value has no users instead of
        // checking the type, since C defaults to returning int for
        // undeclared functions.
        if (!caller->use_empty()) {
          terminateStateOnExecError(state, "return void when caller expected a result");
        }
      }
    }      
    break;
  }
  case Instruction::Br: {
    BranchInst *bi = cast<BranchInst>(i);
    if (bi->isUnconditional()) {
      transferToBasicBlock(bi->getSuccessor(0), bi->getParent(), state);
    } else {
      // FIXME: Find a way that we don't have this hidden dependency.
      assert(bi->getCondition() == bi->getOperand(0) &&
             "Wrong operand index!");
      ref<Expr> cond = eval(ki, 0, state).value;

      cond = optimizer.optimizeExpr(cond, false);
      Executor::StatePair branches = fork(state, cond, false, BranchType::ConditionalBranch);

      // NOTE: There is a hidden dependency here, markBranchVisited
      // requires that we still be in the context of the branch
      // instruction (it reuses its statistic id). Should be cleaned
      // up with convenient instruction specific data.
      if (statsTracker && state.stack.back().kf->trackCoverage)
        statsTracker->markBranchVisited(branches.first, branches.second);

      if (branches.first)
        transferToBasicBlock(bi->getSuccessor(0), bi->getParent(), *branches.first);
      if (branches.second)
        transferToBasicBlock(bi->getSuccessor(1), bi->getParent(), *branches.second);

      if (branches.first && branches.second) {
        branches.first->forkReason = "True branch at " + std::to_string(ki->info->assemblyLine);
        branches.second->forkReason = "False branch at " + std::to_string(ki->info->assemblyLine);
      }

    }
    break;
  }
  case Instruction::IndirectBr: {
    // implements indirect branch to a label within the current function
    const auto bi = cast<IndirectBrInst>(i);
    auto address = eval(ki, 0, state).value;
    address = toUnique(state, address);

    // concrete address
    if (const auto CE = dyn_cast<ConstantExpr>(address.get())) {
      const auto bb_address = (BasicBlock *) CE->getZExtValue(Context::get().getPointerWidth());
      transferToBasicBlock(bb_address, bi->getParent(), state);
      break;
    }

    // symbolic address
    const auto numDestinations = bi->getNumDestinations();
    std::vector<BasicBlock *> targets;
    targets.reserve(numDestinations);
    std::vector<ref<Expr>> expressions;
    expressions.reserve(numDestinations);

    ref<Expr> errorCase = ConstantExpr::alloc(1, Expr::Bool);
    SmallPtrSet<BasicBlock *, 5> destinations;
    // collect and check destinations from label list
    for (unsigned k = 0; k < numDestinations; ++k) {
      // filter duplicates
      const auto d = bi->getDestination(k);
      if (destinations.count(d)) continue;
      destinations.insert(d);

      // create address expression
      const auto PE = Expr::createPointer(reinterpret_cast<std::uint64_t>(d));
      ref<Expr> e = EqExpr::create(address, PE);

      // exclude address from errorCase
      errorCase = AndExpr::create(errorCase, Expr::createIsZero(e));

      // check feasibility
      bool result;
      bool success __attribute__((unused)) =
          solver->mayBeTrue(state.constraints, e, result, state.queryMetaData);
      assert(success && "FIXME: Unhandled solver failure");
      if (result) {
        targets.push_back(d);
        expressions.push_back(e);
      }
    }
    // check errorCase feasibility
    bool result;
    bool success __attribute__((unused)) = solver->mayBeTrue(
        state.constraints, errorCase, result, state.queryMetaData);
    assert(success && "FIXME: Unhandled solver failure");
    if (result) {
      expressions.push_back(errorCase);
    }

    // fork states
    std::vector<ExecutionState *> branches;
    branch(state, expressions, branches, BranchType::IndirectBranch);

    // terminate error state
    if (result) {
      terminateStateOnExecError(*branches.back(), "indirectbr: illegal label address");
      branches.pop_back();
    }

    // branch states to resp. target blocks
    assert(targets.size() == branches.size());
    for (std::vector<ExecutionState *>::size_type k = 0; k < branches.size(); ++k) {
      if (branches[k]) {
        transferToBasicBlock(targets[k], bi->getParent(), *branches[k]);
      }
    }

    break;
  }
  case Instruction::Switch: {
    SwitchInst *si = cast<SwitchInst>(i);
    ref<Expr> cond = eval(ki, 0, state).value;
    BasicBlock *bb = si->getParent();

    cond = toUnique(state, cond);
    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(cond)) {
      // Somewhat gross to create these all the time, but fine till we
      // switch to an internal rep.
      llvm::IntegerType *Ty = cast<IntegerType>(si->getCondition()->getType());
      ConstantInt *ci = ConstantInt::get(Ty, CE->getZExtValue());
      unsigned index = si->findCaseValue(ci)->getSuccessorIndex();
      transferToBasicBlock(si->getSuccessor(index), si->getParent(), state);
    } else {
      // Handle possible different branch targets

      // We have the following assumptions:
      // - each case value is mutual exclusive to all other values
      // - order of case branches is based on the order of the expressions of
      //   the case values, still default is handled last
      std::vector<BasicBlock *> bbOrder;
      std::map<BasicBlock *, ref<Expr> > branchTargets;

      std::map<ref<Expr>, BasicBlock *> expressionOrder;

      // Iterate through all non-default cases and order them by expressions
      for (auto i : si->cases()) {
        ref<Expr> value = evalConstant(i.getCaseValue());

        BasicBlock *caseSuccessor = i.getCaseSuccessor();
        expressionOrder.insert(std::make_pair(value, caseSuccessor));
      }

      // Track default branch values
      ref<Expr> defaultValue = ConstantExpr::alloc(1, Expr::Bool);

      // iterate through all non-default cases but in order of the expressions
      for (std::map<ref<Expr>, BasicBlock *>::iterator
               it = expressionOrder.begin(),
               itE = expressionOrder.end();
           it != itE; ++it) {
        ref<Expr> match = EqExpr::create(cond, it->first);

        // skip if case has same successor basic block as default case
        // (should work even with phi nodes as a switch is a single terminating instruction)
        if (it->second == si->getDefaultDest()) continue;

        // Make sure that the default value does not contain this target's value
        defaultValue = AndExpr::create(defaultValue, Expr::createIsZero(match));

        // Check if control flow could take this case
        bool result;
        match = optimizer.optimizeExpr(match, false);
        bool success = solver->mayBeTrue(state.constraints, match, result,
                                         state.queryMetaData);
        assert(success && "FIXME: Unhandled solver failure");
        (void) success;
        if (result) {
          BasicBlock *caseSuccessor = it->second;

          // Handle the case that a basic block might be the target of multiple
          // switch cases.
          // Currently we generate an expression containing all switch-case
          // values for the same target basic block. We spare us forking too
          // many times but we generate more complex condition expressions
          // TODO Add option to allow to choose between those behaviors
          std::pair<std::map<BasicBlock *, ref<Expr> >::iterator, bool> res =
              branchTargets.insert(std::make_pair(
                  caseSuccessor, ConstantExpr::alloc(0, Expr::Bool)));

          res.first->second = OrExpr::create(match, res.first->second);

          // Only add basic blocks which have not been target of a branch yet
          if (res.second) {
            bbOrder.push_back(caseSuccessor);
          }
        }
      }

      // Check if control could take the default case
      defaultValue = optimizer.optimizeExpr(defaultValue, false);
      bool res;
      bool success = solver->mayBeTrue(state.constraints, defaultValue, res,
                                       state.queryMetaData);
      assert(success && "FIXME: Unhandled solver failure");
      (void) success;
      if (res) {
        std::pair<std::map<BasicBlock *, ref<Expr> >::iterator, bool> ret =
            branchTargets.insert(
                std::make_pair(si->getDefaultDest(), defaultValue));
        if (ret.second) {
          bbOrder.push_back(si->getDefaultDest());
        }
      }

      // Fork the current state with each state having one of the possible
      // successors of this switch
      std::vector< ref<Expr> > conditions;
      for (std::vector<BasicBlock *>::iterator it = bbOrder.begin(),
                                               ie = bbOrder.end();
           it != ie; ++it) {
        conditions.push_back(branchTargets[*it]);
      }
      std::vector<ExecutionState*> branches;
      branch(state, conditions, branches, BranchType::Switch);

      std::vector<ExecutionState*>::iterator bit = branches.begin();
      for (std::vector<BasicBlock *>::iterator it = bbOrder.begin(),
                                               ie = bbOrder.end();
           it != ie; ++it) {
        ExecutionState *es = *bit;
        if (es)
          transferToBasicBlock(*it, bb, *es);
        ++bit;
      }
    }
    break;
  }
  case Instruction::Unreachable:
    // Note that this is not necessarily an internal bug, llvm will
    // generate unreachable instructions in cases where it knows the
    // program will crash. So it is effectively a SEGV or internal
    // error.
    terminateStateOnExecError(state, "reached \"unreachable\" instruction");
    break;

  case Instruction::Invoke:
  case Instruction::Call: {
    // Ignore debug intrinsic calls
    if (isa<DbgInfoIntrinsic>(i))
      break;

#if LLVM_VERSION_CODE >= LLVM_VERSION(8, 0)
    const CallBase &cs = cast<CallBase>(*i);
    Value *fp = cs.getCalledOperand();
#else
    const CallSite cs(i);
    Value *fp = cs.getCalledValue();
#endif

    unsigned numArgs = cs.arg_size();
    Function *f = getTargetFunction(fp, state);

    if (isa<InlineAsm>(fp)) {
      terminateStateOnExecError(state, "inline assembly is unsupported");
      break;
    }

    if (f && !state.hasMadeSmokeTest) {
      if (apiFunctions.end() != std::find(apiFunctions.begin(),
                                          apiFunctions.end(),
                                          f->getName().str())) {
        for (int index = 0; index < maxSmokeTestCount; index++) {
          std::vector<std::string> failedVariables;
          bool hasSuccess = false;
          ExecutionState *eq_state = state.branch();
          for (const std::pair<const MemoryObject *, ref<ObjectState>> &entry :
               eq_state->addressSpace.objects) {
            trySolveVariableInSmokeTest(state, failedVariables, hasSuccess,
                                        eq_state, entry);
          }

          for (const std::pair<const MemoryObject *, ref<ObjectState>> &entry :
               eq_state->heap.objects) {
            trySolveVariableInSmokeTest(state, failedVariables, hasSuccess,
                                        eq_state, entry);
          }

          if (!failedVariables.empty()) {
            // print all failed variables
            klee_message("\033[31m failed variables: \033[0m");
            for (auto &name : failedVariables) {
              klee_message("\033[31m %s \033[0m", name.c_str());
            }
          }
          if (!hasSuccess) {
            klee_message("\033[31mFailed to get values for all variables, "
                         "smoke test is going to stop\033[0m");
            break;
          }
          eq_state->hasMadeSmokeTest = true;
          addedStates.push_back(eq_state);
          processTree->attach(state.ptreeNode, eq_state, &state,
                              BranchType::ConditionalBranch);
          transferToBasicBlock(i->getParent(), i->getParent()->getPrevNode(),
                               *eq_state);
          // state's pc is now the next instruction of the function call
          eq_state->pc = state.prevPC;
          klee_message("....start execute %dth smoke test....", index);
          klee_message("|\tName\t|\tValue\t|");
          for (const std::pair<const MemoryObject *, ref<ObjectState>> &entry :
               eq_state->addressSpace.objects) {
            if (entry.first->name == "unnamed")
              continue;
            uint64_t value = 0ull;
            for (unsigned offset = 0; offset < entry.second->size; offset++) {
              uint64_t tmp = entry.second->getConcrete(offset);
              value += tmp << (offset * 8);
            }
            klee_message("|\t%s\t|\t0x%lx\t|", entry.first->name.c_str(),
                         value);
          }
          while (eq_state &&
                 addedStates.end() != std::find(addedStates.begin(),
                                                addedStates.end(), eq_state) &&
                 eq_state->pc) {
            KInstruction *eq_ki = eq_state->pc;
            stepInstruction(*eq_state);
            executeInstruction(*eq_state, eq_ki);
          }
        }
        terminateState(state);
      }
    }

    // evaluate arguments
    std::vector< ref<Expr> > arguments;
    arguments.reserve(numArgs);

    for (unsigned j=0; j<numArgs; ++j)
      arguments.push_back(eval(ki, j+1, state).value);

    if (f) {
      const FunctionType *fType = 
        dyn_cast<FunctionType>(cast<PointerType>(f->getType())->getElementType());
      const FunctionType *fpType =
        dyn_cast<FunctionType>(cast<PointerType>(fp->getType())->getElementType());

      // special case the call with a bitcast case
      if (fType != fpType) {
        assert(fType && fpType && "unable to get function type");

        // XXX check result coercion

        // XXX this really needs thought and validation
        unsigned i=0;
        for (std::vector< ref<Expr> >::iterator
               ai = arguments.begin(), ie = arguments.end();
             ai != ie; ++ai) {
          Expr::Width to, from = (*ai)->getWidth();
            
          if (i<fType->getNumParams()) {
            to = getWidthForLLVMType(fType->getParamType(i));

            if (from != to) {
              // XXX need to check other param attrs ?
              bool isSExt = cs.paramHasAttr(i, llvm::Attribute::SExt);
              if (isSExt) {
                arguments[i] = SExtExpr::create(arguments[i], to);
              } else {
                arguments[i] = ZExtExpr::create(arguments[i], to);
              }
            }
          }
            
          i++;
        }
      }

      executeCall(state, ki, f, arguments);
    } else {
      ref<Expr> v = eval(ki, 0, state).value;

      ExecutionState *free = &state;
      bool hasInvalid = false, first = true;

      /* XXX This is wasteful, no need to do a full evaluate since we
         have already got a value. But in the end the caches should
         handle it for us, albeit with some overhead. */
      do {
        v = optimizer.optimizeExpr(v, true);
        // try a TPot optimiization to concretize the address
        v = ConstraintManager::simplifyReads(solver->solver.get(), state.constraints, v);
        ref<ConstantExpr> value;
        bool success =
            solver->getValue(free->constraints, v, value, free->queryMetaData);
        assert(success && "FIXME: Unhandled solver failure");
        (void) success;
        StatePair res = fork(*free, EqExpr::create(v, value), true, BranchType::Call);
        if (res.first) {
          uint64_t addr = value->getZExtValue();
          auto it = legalFunctions.find(addr);
          if (it != legalFunctions.end()) {
            f = it->second;

            // Don't give warning on unique resolution
            if (res.second || !first)
              klee_warning_once(reinterpret_cast<void*>(addr),
                                "resolved symbolic function pointer to: %s",
                                f->getName().data());

            executeCall(*res.first, ki, f, arguments);
          } else {
            if (!hasInvalid) {
              terminateStateOnExecError(state, "invalid function pointer");
              hasInvalid = true;
            }
          }
        }

        first = false;
        free = res.second;
      } while (free);
    }
    break;
  }
  case Instruction::PHI: {
    // First, execute the PHI node
    ref<Expr> result = eval(ki, state.incomingBBIndex, state).value;
    bindLocal(ki, state, result);

    if (!InductiveSymbex)
      break; 


    // The commented out block below is an old implementation of loop invariants.

    // // Assumption: loops start with PHI nodes
    // BasicBlock *curBB = i->getParent();
    // KFunction *kf = kmodule->functionMap[curBB->getParent()];
    // if(kf->loopInfo->isLoopHeader(curBB)) {

    //   // Assumption: the only modified variable is the PHI node target.
    //   std::vector<KInstruction *> modifiedVars;
    //   modifiedVars.push_back(ki);

    //   // check if we have already summarized this loop
    //   auto it = curLoopInvariants.find(curBB);
    //   if (it == curLoopInvariants.end()) {
    //     // pick a hint to construct a candidate invariant.
    //     assert(assumeForallHints.size() > 0 && "No hints for loop invariant generation");
    //     Function *hint = assumeForallHints[0];

    //     ref<Expr> inv = invSchema_0(state, hint, modifiedVars);

    //     // BASE CASE: Does the loop invariant hold initially?
    //     bool success = false;
    //     solver->setTimeout(coreSolverTimeout);
    //     bool solver_success = solver->mustBeTrue(state.constraints, inv, success,
    //                                       state.queryMetaData);
    //     solver->setTimeout(time::Span());
    //     if (!solver_success) {
    //       state.pc = state.prevPC;
    //       terminateStateOnSolverError(state, "Query timed out (loop invariant base case).");
    //       return;
    //     }

    //     if (success) {
    //       klee_message("Loop invariant holds initially");
    //       curLoopInvariants[curBB] = std::make_pair(hint, 0);
    //     } else {
    //       klee_warning("Loop invariant does not hold initially");
    //       // TODO! Try other invariants.
    //     }

    //     // Make modified state symbolic to overestimate the set of all reachable states.
    //     for (auto m: modifiedVars) {
    //       KInstruction *kinstr = m;
    //       ref<Expr> value = getDestCell(state, kinstr).value;

    //       ref<Expr> symbolic = BitVecExpr::create("syt_stack_" + \
    //         std::to_string(kinstr->info->assemblyLine) + "_prime" + \
    //         "(" + curBB->getParent()->getName().str() + ")", value->getWidth());
    //       bindLocal(kinstr, state, symbolic);
    //     }

    //     // Add the loop invariant over the symbolic state.
    //     ref<Expr> inv_over_symb = invSchema_0(state, hint, modifiedVars);
    //     addConstraint(state, inv_over_symb);

    //   } else {
    //     // The loop body has already been executed.

    //     // INDUCTION STEP: Does the loop invariant hold after one iteration?
    //     auto hint = it->second.first;
    //     ref<Expr> inv = invSchema_0(state, hint, modifiedVars);

    //     bool success = false;
    //     solver->setTimeout(coreSolverTimeout);
    //     bool solver_success = solver->mustBeTrue(state.constraints, inv, success,
    //                                       state.queryMetaData);
    //     solver->setTimeout(time::Span());
    //     if (!solver_success) {
    //       state.pc = state.prevPC;
    //       terminateStateOnSolverError(state, "Query timed out (loop invariant induction case).");
    //       return;
    //     }

    //     if (success) {
    //       klee_message("Loop invariant is maintained");
    //       interpreterHandler->incPathsCompleted();
    //       terminateState(state);
    //     } else {
    //       klee_warning("Loop invariant is not maintained");
    //       // TODO! Try other invariants.
    //     }
    //   }
    // }

    break;
  }

    // Special instructions
  case Instruction::Select: {
    // NOTE: It is not required that operands 1 and 2 be of scalar type.
    ref<Expr> cond = eval(ki, 0, state).value;
    ref<Expr> tExpr = eval(ki, 1, state).value;
    ref<Expr> fExpr = eval(ki, 2, state).value;
    ref<Expr> result = SelectExpr::create(cond, tExpr, fExpr);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::VAArg:
    terminateStateOnExecError(state, "unexpected VAArg instruction");
    break;

    // Arithmetic / logical

  case Instruction::Add: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    bindLocal(ki, state, AddExpr::create(left, right));
    break;
  }

  case Instruction::Sub: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    bindLocal(ki, state, SubExpr::create(left, right));
    break;
  }
 
  case Instruction::Mul: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    bindLocal(ki, state, MulExpr::create(left, right));
    break;
  }

  case Instruction::UDiv: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = UDivExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::SDiv: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = SDivExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::URem: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = URemExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::SRem: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = SRemExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::And: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = AndExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::Or: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = OrExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::Xor: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = XorExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::Shl: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = ShlExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::LShr: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = LShrExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::AShr: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = AShrExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

    // Compare

  case Instruction::ICmp: {
    CmpInst *ci = cast<CmpInst>(i);
    ICmpInst *ii = cast<ICmpInst>(ci);

    switch(ii->getPredicate()) {
    case ICmpInst::ICMP_EQ: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = EqExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_NE: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = NeExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_UGT: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = UgtExpr::create(left, right);
      bindLocal(ki, state,result);
      break;
    }

    case ICmpInst::ICMP_UGE: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = UgeExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_ULT: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = UltExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_ULE: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = UleExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_SGT: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = SgtExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_SGE: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = SgeExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_SLT: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = SltExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_SLE: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = SleExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    default:
      terminateStateOnExecError(state, "invalid ICmp predicate");
    }
    break;
  }
 
    // Memory instructions...
  case Instruction::Alloca: {
    AllocaInst *ai = cast<AllocaInst>(i);
    unsigned elementSize = 
      kmodule->targetData->getTypeStoreSize(ai->getAllocatedType());
    ref<Expr> size = Expr::createPointer(elementSize);
    if (ai->isArrayAllocation()) {
      ref<Expr> count = eval(ki, 0, state).value;
      count = Expr::createZExtToPointerWidth(count);
      size = MulExpr::create(size, count);
    }
    executeAlloc(state, size, true, ki);
    break;
  }

  case Instruction::Load: {
    ref<Expr> base = eval(ki, 0, state).value;
    executeMemoryOperation(state, MEMOP_READ, base, 0, ki, 0, "");
    break;
  }
  case Instruction::Store: {
    ref<Expr> base = eval(ki, 1, state).value;
    ref<Expr> value = eval(ki, 0, state).value;
    executeMemoryOperation(state, MEMOP_WRITE, base, value, 0, 0, "");
    break;
  }

  case Instruction::GetElementPtr: {
    KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);
    ref<Expr> base = eval(ki, 0, state).value;

    for (std::vector< std::pair<unsigned, uint64_t> >::iterator 
           it = kgepi->indices.begin(), ie = kgepi->indices.end(); 
         it != ie; ++it) {
      uint64_t elementSize = it->second;
      ref<Expr> index = eval(ki, it->first, state).value;
      base = AddExpr::create(base,
                             MulExpr::create(Expr::createSExtToPointerWidth(index),
                                             Expr::createPointer(elementSize)));
    }
    if (kgepi->offset)
      base = AddExpr::create(base,
                             Expr::createPointer(kgepi->offset));
    bindLocal(ki, state, base);
    break;
  }

    // Conversion
  case Instruction::Trunc: {
    CastInst *ci = cast<CastInst>(i);
    ref<Expr> result = ExtractExpr::create(eval(ki, 0, state).value,
                                           0,
                                           getWidthForLLVMType(ci->getType()));
    bindLocal(ki, state, result);
    break;
  }
  case Instruction::ZExt: {
    CastInst *ci = cast<CastInst>(i);
    ref<Expr> result = ZExtExpr::create(eval(ki, 0, state).value,
                                        getWidthForLLVMType(ci->getType()));
    bindLocal(ki, state, result);
    break;
  }
  case Instruction::SExt: {
    CastInst *ci = cast<CastInst>(i);
    ref<Expr> result = SExtExpr::create(eval(ki, 0, state).value,
                                        getWidthForLLVMType(ci->getType()));
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::IntToPtr: {
    CastInst *ci = cast<CastInst>(i);
    Expr::Width pType = getWidthForLLVMType(ci->getType());
    ref<Expr> arg = eval(ki, 0, state).value;
    bindLocal(ki, state, ZExtExpr::create(arg, pType));
    break;
  }
  case Instruction::PtrToInt: {
    CastInst *ci = cast<CastInst>(i);
    Expr::Width iType = getWidthForLLVMType(ci->getType());
    ref<Expr> arg = eval(ki, 0, state).value;
    assert(arg->getWidth() != 0); // don't zext integer expressions.
    bindLocal(ki, state, ZExtExpr::create(arg, iType));
    break;
  }

  case Instruction::BitCast: {
    ref<Expr> result = eval(ki, 0, state).value;
    bindLocal(ki, state, result);
    break;
  }

    // Floating point instructions

#if LLVM_VERSION_CODE >= LLVM_VERSION(8, 0)
  case Instruction::FNeg: {
    ref<ConstantExpr> arg =
        toConstant(state, eval(ki, 0, state).value, "floating point");
    if (!fpWidthToSemantics(arg->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FNeg operation");

    llvm::APFloat Res(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
    Res = llvm::neg(Res);
    bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    break;
  }
#endif

  case Instruction::FAdd: {
    ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
                                        "floating point");
    ref<ConstantExpr> right = toConstant(state, eval(ki, 1, state).value,
                                         "floating point");
    if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FAdd operation");

    llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
    Res.add(APFloat(*fpWidthToSemantics(right->getWidth()),right->getAPValue()), APFloat::rmNearestTiesToEven);
    bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    break;
  }

  case Instruction::FSub: {
    ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
                                        "floating point");
    ref<ConstantExpr> right = toConstant(state, eval(ki, 1, state).value,
                                         "floating point");
    if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FSub operation");
    llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
    Res.subtract(APFloat(*fpWidthToSemantics(right->getWidth()), right->getAPValue()), APFloat::rmNearestTiesToEven);
    bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    break;
  }

  case Instruction::FMul: {
    ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
                                        "floating point");
    ref<ConstantExpr> right = toConstant(state, eval(ki, 1, state).value,
                                         "floating point");
    if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FMul operation");

    llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
    Res.multiply(APFloat(*fpWidthToSemantics(right->getWidth()), right->getAPValue()), APFloat::rmNearestTiesToEven);
    bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    break;
  }

  case Instruction::FDiv: {
    ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
                                        "floating point");
    ref<ConstantExpr> right = toConstant(state, eval(ki, 1, state).value,
                                         "floating point");
    if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FDiv operation");

    llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
    Res.divide(APFloat(*fpWidthToSemantics(right->getWidth()), right->getAPValue()), APFloat::rmNearestTiesToEven);
    bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    break;
  }

  case Instruction::FRem: {
    ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
                                        "floating point");
    ref<ConstantExpr> right = toConstant(state, eval(ki, 1, state).value,
                                         "floating point");
    if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FRem operation");
    llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
    Res.mod(
        APFloat(*fpWidthToSemantics(right->getWidth()), right->getAPValue()));
    bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    break;
  }

  case Instruction::FPTrunc: {
    FPTruncInst *fi = cast<FPTruncInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
                                       "floating point");
    if (!fpWidthToSemantics(arg->getWidth()) || resultType > arg->getWidth())
      return terminateStateOnExecError(state, "Unsupported FPTrunc operation");

    llvm::APFloat Res(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
    bool losesInfo = false;
    Res.convert(*fpWidthToSemantics(resultType),
                llvm::APFloat::rmNearestTiesToEven,
                &losesInfo);
    bindLocal(ki, state, ConstantExpr::alloc(Res));
    break;
  }

  case Instruction::FPExt: {
    FPExtInst *fi = cast<FPExtInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
                                        "floating point");
    if (!fpWidthToSemantics(arg->getWidth()) || arg->getWidth() > resultType)
      return terminateStateOnExecError(state, "Unsupported FPExt operation");
    llvm::APFloat Res(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
    bool losesInfo = false;
    Res.convert(*fpWidthToSemantics(resultType),
                llvm::APFloat::rmNearestTiesToEven,
                &losesInfo);
    bindLocal(ki, state, ConstantExpr::alloc(Res));
    break;
  }

  case Instruction::FPToUI: {
    FPToUIInst *fi = cast<FPToUIInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
                                       "floating point");
    if (!fpWidthToSemantics(arg->getWidth()) || resultType > 64)
      return terminateStateOnExecError(state, "Unsupported FPToUI operation");

    llvm::APFloat Arg(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
    uint64_t value = 0;
    bool isExact = true;
    auto valueRef = makeMutableArrayRef(value);
    Arg.convertToInteger(valueRef, resultType, false,
                         llvm::APFloat::rmTowardZero, &isExact);
    bindLocal(ki, state, ConstantExpr::alloc(value, resultType));
    break;
  }

  case Instruction::FPToSI: {
    FPToSIInst *fi = cast<FPToSIInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
                                       "floating point");
    if (!fpWidthToSemantics(arg->getWidth()) || resultType > 64)
      return terminateStateOnExecError(state, "Unsupported FPToSI operation");
    llvm::APFloat Arg(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());

    uint64_t value = 0;
    bool isExact = true;
    auto valueRef = makeMutableArrayRef(value);
    Arg.convertToInteger(valueRef, resultType, true,
                         llvm::APFloat::rmTowardZero, &isExact);
    bindLocal(ki, state, ConstantExpr::alloc(value, resultType));
    break;
  }

  case Instruction::UIToFP: {
    UIToFPInst *fi = cast<UIToFPInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
                                       "floating point");
    const llvm::fltSemantics *semantics = fpWidthToSemantics(resultType);
    if (!semantics)
      return terminateStateOnExecError(state, "Unsupported UIToFP operation");
    llvm::APFloat f(*semantics, 0);
    f.convertFromAPInt(arg->getAPValue(), false,
                       llvm::APFloat::rmNearestTiesToEven);

    bindLocal(ki, state, ConstantExpr::alloc(f));
    break;
  }

  case Instruction::SIToFP: {
    SIToFPInst *fi = cast<SIToFPInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
                                       "floating point");
    const llvm::fltSemantics *semantics = fpWidthToSemantics(resultType);
    if (!semantics)
      return terminateStateOnExecError(state, "Unsupported SIToFP operation");
    llvm::APFloat f(*semantics, 0);
    f.convertFromAPInt(arg->getAPValue(), true,
                       llvm::APFloat::rmNearestTiesToEven);

    bindLocal(ki, state, ConstantExpr::alloc(f));
    break;
  }

  case Instruction::FCmp: {
    FCmpInst *fi = cast<FCmpInst>(i);
    ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
                                        "floating point");
    ref<ConstantExpr> right = toConstant(state, eval(ki, 1, state).value,
                                         "floating point");
    if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FCmp operation");

    APFloat LHS(*fpWidthToSemantics(left->getWidth()),left->getAPValue());
    APFloat RHS(*fpWidthToSemantics(right->getWidth()),right->getAPValue());
    APFloat::cmpResult CmpRes = LHS.compare(RHS);

    bool Result = false;
    switch( fi->getPredicate() ) {
      // Predicates which only care about whether or not the operands are NaNs.
    case FCmpInst::FCMP_ORD:
      Result = (CmpRes != APFloat::cmpUnordered);
      break;

    case FCmpInst::FCMP_UNO:
      Result = (CmpRes == APFloat::cmpUnordered);
      break;

      // Ordered comparisons return false if either operand is NaN.  Unordered
      // comparisons return true if either operand is NaN.
    case FCmpInst::FCMP_UEQ:
      Result = (CmpRes == APFloat::cmpUnordered || CmpRes == APFloat::cmpEqual);
      break;
    case FCmpInst::FCMP_OEQ:
      Result = (CmpRes != APFloat::cmpUnordered && CmpRes == APFloat::cmpEqual);
      break;

    case FCmpInst::FCMP_UGT:
      Result = (CmpRes == APFloat::cmpUnordered || CmpRes == APFloat::cmpGreaterThan);
      break;
    case FCmpInst::FCMP_OGT:
      Result = (CmpRes != APFloat::cmpUnordered && CmpRes == APFloat::cmpGreaterThan);
      break;

    case FCmpInst::FCMP_UGE:
      Result = (CmpRes == APFloat::cmpUnordered || (CmpRes == APFloat::cmpGreaterThan || CmpRes == APFloat::cmpEqual));
      break;
    case FCmpInst::FCMP_OGE:
      Result = (CmpRes != APFloat::cmpUnordered && (CmpRes == APFloat::cmpGreaterThan || CmpRes == APFloat::cmpEqual));
      break;

    case FCmpInst::FCMP_ULT:
      Result = (CmpRes == APFloat::cmpUnordered || CmpRes == APFloat::cmpLessThan);
      break;
    case FCmpInst::FCMP_OLT:
      Result = (CmpRes != APFloat::cmpUnordered && CmpRes == APFloat::cmpLessThan);
      break;

    case FCmpInst::FCMP_ULE:
      Result = (CmpRes == APFloat::cmpUnordered || (CmpRes == APFloat::cmpLessThan || CmpRes == APFloat::cmpEqual));
      break;
    case FCmpInst::FCMP_OLE:
      Result = (CmpRes != APFloat::cmpUnordered && (CmpRes == APFloat::cmpLessThan || CmpRes == APFloat::cmpEqual));
      break;

    case FCmpInst::FCMP_UNE:
      Result = (CmpRes == APFloat::cmpUnordered || CmpRes != APFloat::cmpEqual);
      break;
    case FCmpInst::FCMP_ONE:
      Result = (CmpRes != APFloat::cmpUnordered && CmpRes != APFloat::cmpEqual);
      break;

    default:
      assert(0 && "Invalid FCMP predicate!");
      break;
    case FCmpInst::FCMP_FALSE:
      Result = false;
      break;
    case FCmpInst::FCMP_TRUE:
      Result = true;
      break;
    }

    bindLocal(ki, state, ConstantExpr::alloc(Result, Expr::Bool));
    break;
  }
  case Instruction::InsertValue: {
    KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);

    ref<Expr> agg = eval(ki, 0, state).value;
    ref<Expr> val = eval(ki, 1, state).value;

    ref<Expr> l = NULL, r = NULL;
    unsigned lOffset = kgepi->offset*8, rOffset = kgepi->offset*8 + val->getWidth();

    if (lOffset > 0)
      l = ExtractExpr::create(agg, 0, lOffset);
    if (rOffset < agg->getWidth())
      r = ExtractExpr::create(agg, rOffset, agg->getWidth() - rOffset);

    ref<Expr> result;
    if (l && r)
      result = ConcatExpr::create(r, ConcatExpr::create(val, l));
    else if (l)
      result = ConcatExpr::create(val, l);
    else if (r)
      result = ConcatExpr::create(r, val);
    else
      result = val;

    bindLocal(ki, state, result);
    break;
  }
  case Instruction::ExtractValue: {
    KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);

    ref<Expr> agg = eval(ki, 0, state).value;

    ref<Expr> result = ExtractExpr::create(agg, kgepi->offset*8, getWidthForLLVMType(i->getType()));

    bindLocal(ki, state, result);
    break;
  }
  case Instruction::Fence: {
    // Ignore for now
    break;
  }
  case Instruction::InsertElement: {
    InsertElementInst *iei = cast<InsertElementInst>(i);
    ref<Expr> vec = eval(ki, 0, state).value;
    ref<Expr> newElt = eval(ki, 1, state).value;
    ref<Expr> idx = eval(ki, 2, state).value;

    ConstantExpr *cIdx = dyn_cast<ConstantExpr>(idx);
    if (cIdx == NULL) {
      terminateStateOnExecError(
          state, "InsertElement, support for symbolic index not implemented");
      return;
    }
    uint64_t iIdx = cIdx->getZExtValue();
#if LLVM_VERSION_MAJOR >= 11
    const auto *vt = cast<llvm::FixedVectorType>(iei->getType());
#else
    const llvm::VectorType *vt = iei->getType();
#endif
    unsigned EltBits = getWidthForLLVMType(vt->getElementType());

    if (iIdx >= vt->getNumElements()) {
      // Out of bounds write
      terminateStateOnError(state, "Out of bounds write when inserting element",
                            StateTerminationType::BadVectorAccess);
      return;
    }

    const unsigned elementCount = vt->getNumElements();
    llvm::SmallVector<ref<Expr>, 8> elems;
    elems.reserve(elementCount);
    for (unsigned i = elementCount; i != 0; --i) {
      auto of = i - 1;
      unsigned bitOffset = EltBits * of;
      elems.push_back(
          of == iIdx ? newElt : ExtractExpr::create(vec, bitOffset, EltBits));
    }

    assert(Context::get().isLittleEndian() && "FIXME:Broken for big endian");
    ref<Expr> Result = ConcatExpr::createN(elementCount, elems.data());
    bindLocal(ki, state, Result);
    break;
  }
  case Instruction::ExtractElement: {
    ExtractElementInst *eei = cast<ExtractElementInst>(i);
    ref<Expr> vec = eval(ki, 0, state).value;
    ref<Expr> idx = eval(ki, 1, state).value;

    ConstantExpr *cIdx = dyn_cast<ConstantExpr>(idx);
    if (cIdx == NULL) {
      terminateStateOnExecError(
          state, "ExtractElement, support for symbolic index not implemented");
      return;
    }
    uint64_t iIdx = cIdx->getZExtValue();
#if LLVM_VERSION_MAJOR >= 11
    const auto *vt = cast<llvm::FixedVectorType>(eei->getVectorOperandType());
#else
    const llvm::VectorType *vt = eei->getVectorOperandType();
#endif
    unsigned EltBits = getWidthForLLVMType(vt->getElementType());

    if (iIdx >= vt->getNumElements()) {
      // Out of bounds read
      terminateStateOnError(state, "Out of bounds read when extracting element",
                            StateTerminationType::BadVectorAccess);
      return;
    }

    unsigned bitOffset = EltBits * iIdx;
    ref<Expr> Result = ExtractExpr::create(vec, bitOffset, EltBits);
    bindLocal(ki, state, Result);
    break;
  }
  case Instruction::ShuffleVector:
    // Should never happen due to Scalarizer pass removing ShuffleVector
    // instructions.
    terminateStateOnExecError(state, "Unexpected ShuffleVector instruction");
    break;

#ifdef SUPPORT_KLEE_EH_CXX
  case Instruction::Resume: {
    auto *cui = dyn_cast_or_null<CleanupPhaseUnwindingInformation>(
        state.unwindingInformation.get());

    if (!cui) {
      terminateStateOnExecError(
          state,
          "resume-instruction executed outside of cleanup phase unwinding");
      break;
    }

    ref<Expr> arg = eval(ki, 0, state).value;
    ref<Expr> exceptionPointer = ExtractExpr::create(arg, 0, Expr::Int64);
    ref<Expr> selectorValue =
        ExtractExpr::create(arg, Expr::Int64, Expr::Int32);

    if (!dyn_cast<ConstantExpr>(exceptionPointer) ||
        !dyn_cast<ConstantExpr>(selectorValue)) {
      terminateStateOnExecError(
          state, "resume-instruction called with non constant expression");
      break;
    }

    if (!Expr::createIsZero(selectorValue)->isTrue()) {
      klee_warning("resume-instruction called with non-0 selector value");
    }

    if (!EqExpr::create(exceptionPointer, cui->exceptionObject)->isTrue()) {
      terminateStateOnExecError(
          state, "resume-instruction called with unexpected exception pointer");
      break;
    }

    unwindToNextLandingpad(state);
    break;
  }

  case Instruction::LandingPad: {
    auto *cui = dyn_cast_or_null<CleanupPhaseUnwindingInformation>(
        state.unwindingInformation.get());

    if (!cui) {
      terminateStateOnExecError(
          state, "Executing landing pad but not in unwinding phase 2");
      break;
    }

    ref<ConstantExpr> exceptionPointer = cui->exceptionObject;
    ref<ConstantExpr> selectorValue;

    // check on which frame we are currently
    if (state.stack.size() - 1 == cui->catchingStackIndex) {
      // we are in the target stack frame, return the selector value
      // that was returned by the personality fn in phase 1 and stop unwinding.
      selectorValue = cui->selectorValue;

      // stop unwinding by cleaning up our unwinding information.
      state.unwindingInformation.reset();

      // this would otherwise now be a dangling pointer
      cui = nullptr;
    } else {
      // we are not yet at the target stack frame. the landingpad might have
      // a cleanup clause or not, anyway, we give it the selector value "0",
      // which represents a cleanup, and expect it to handle it.
      // This is explicitly allowed by LLVM, see
      // https://llvm.org/docs/ExceptionHandling.html#id18
      selectorValue = ConstantExpr::create(0, Expr::Int32);
    }

    // we have to return a {i8*, i32}
    ref<Expr> result = ConcatExpr::create(
        ZExtExpr::create(selectorValue, Expr::Int32), exceptionPointer);

    bindLocal(ki, state, result);

    break;
  }
#endif // SUPPORT_KLEE_EH_CXX

  case Instruction::AtomicRMW:
    terminateStateOnExecError(state, "Unexpected Atomic instruction, should be "
                                     "lowered by LowerAtomicInstructionPass");
    break;
  case Instruction::AtomicCmpXchg:
    terminateStateOnExecError(state,
                              "Unexpected AtomicCmpXchg instruction, should be "
                              "lowered by LowerAtomicInstructionPass");
    break;
  // Other instructions...
  // Unhandled
  default:
    terminateStateOnExecError(state, "illegal instruction");
    break;
  }
}

void Executor::updateStates(ExecutionState *current) {
  if (searcher) {
    searcher->update(current, addedStates, removedStates);
  }
  
  states.insert(addedStates.begin(), addedStates.end());
  addedStates.clear();

  for (std::vector<ExecutionState *>::iterator it = removedStates.begin(),
                                               ie = removedStates.end();
       it != ie; ++it) {
    ExecutionState *es = *it;
    std::set<ExecutionState*>::iterator it2 = states.find(es);
    assert(it2!=states.end());
    states.erase(it2);
    std::map<ExecutionState*, std::vector<SeedInfo> >::iterator it3 = 
      seedMap.find(es);
    if (it3 != seedMap.end())
      seedMap.erase(it3);
    processTree->remove(es->ptreeNode);
    delete es;
  }
  removedStates.clear();
}

template <typename SqType, typename TypeIt>
void Executor::computeOffsetsSeqTy(KGEPInstruction *kgepi,
                                   ref<ConstantExpr> &constantOffset,
                                   uint64_t index, const TypeIt it) {
  const auto *sq = cast<SqType>(*it);
  uint64_t elementSize =
      kmodule->targetData->getTypeStoreSize(sq->getElementType());
  const Value *operand = it.getOperand();
  if (const Constant *c = dyn_cast<Constant>(operand)) {
    ref<ConstantExpr> index =
        evalConstant(c)->SExt(Context::get().getPointerWidth());
    ref<ConstantExpr> addend = index->Mul(
        ConstantExpr::alloc(elementSize, Context::get().getPointerWidth()));
    constantOffset = constantOffset->Add(addend);
  } else {
    kgepi->indices.emplace_back(index, elementSize);
  }
}

template <typename TypeIt>
void Executor::computeOffsets(KGEPInstruction *kgepi, TypeIt ib, TypeIt ie) {
  ref<ConstantExpr> constantOffset =
    ConstantExpr::alloc(0, Context::get().getPointerWidth());
  uint64_t index = 1;
  for (TypeIt ii = ib; ii != ie; ++ii) {
    if (StructType *st = dyn_cast<StructType>(*ii)) {
      const StructLayout *sl = kmodule->targetData->getStructLayout(st);
      const ConstantInt *ci = cast<ConstantInt>(ii.getOperand());
      uint64_t addend = sl->getElementOffset((unsigned) ci->getZExtValue());
      constantOffset = constantOffset->Add(ConstantExpr::alloc(addend,
                                                               Context::get().getPointerWidth()));
    } else if (isa<ArrayType>(*ii)) {
      computeOffsetsSeqTy<ArrayType>(kgepi, constantOffset, index, ii);
    } else if (isa<VectorType>(*ii)) {
      computeOffsetsSeqTy<VectorType>(kgepi, constantOffset, index, ii);
    } else if (isa<PointerType>(*ii)) {
      computeOffsetsSeqTy<PointerType>(kgepi, constantOffset, index, ii);
    } else
      assert("invalid type" && 0);
    index++;
  }
  kgepi->offset = constantOffset->getZExtValue();
}

void Executor::bindInstructionConstants(KInstruction *KI) {
  if (GetElementPtrInst *gepi = dyn_cast<GetElementPtrInst>(KI->inst)) {
    KGEPInstruction *kgepi = static_cast<KGEPInstruction *>(KI);
    computeOffsets(kgepi, gep_type_begin(gepi), gep_type_end(gepi));
  } else if (InsertValueInst *ivi = dyn_cast<InsertValueInst>(KI->inst)) {
    KGEPInstruction *kgepi = static_cast<KGEPInstruction *>(KI);
    computeOffsets(kgepi, iv_type_begin(ivi), iv_type_end(ivi));
    assert(kgepi->indices.empty() && "InsertValue constant offset expected");
  } else if (ExtractValueInst *evi = dyn_cast<ExtractValueInst>(KI->inst)) {
    KGEPInstruction *kgepi = static_cast<KGEPInstruction *>(KI);
    computeOffsets(kgepi, ev_type_begin(evi), ev_type_end(evi));
    assert(kgepi->indices.empty() && "ExtractValue constant offset expected");
  }
}

void Executor::bindModuleConstants() {
  for (auto &kfp : kmodule->functions) {
    KFunction *kf = kfp.get();
    for (unsigned i=0; i<kf->numInstructions; ++i)
      bindInstructionConstants(kf->instructions[i]);
  }

  kmodule->constantTable =
      std::unique_ptr<Cell[]>(new Cell[kmodule->constants.size()]);
  for (unsigned i=0; i<kmodule->constants.size(); ++i) {
    Cell &c = kmodule->constantTable[i];
    c.value = evalConstantTpotWrapper(kmodule->constants[i]);
  }
}

bool Executor::checkMemoryUsage() {
  if (!MaxMemory) return true;

  // We need to avoid calling GetTotalMallocUsage() often because it
  // is O(elts on freelist). This is really bad since we start
  // to pummel the freelist once we hit the memory cap.
  if ((stats::instructions & 0xFFFFU) != 0) // every 65536 instructions
    return true;

  // check memory limit
  const auto mallocUsage = util::GetTotalMallocUsage() >> 20U;
  const auto mmapUsage = memory->getUsedDeterministicSize() >> 20U;
  const auto totalUsage = mallocUsage + mmapUsage;
  atMemoryLimit = totalUsage > MaxMemory; // inhibit forking
  if (!atMemoryLimit)
    return true;

  // only terminate states when threshold (+100MB) exceeded
  if (totalUsage <= MaxMemory + 100)
    return true;

  // just guess at how many to kill
  const auto numStates = states.size();
  auto toKill = std::max(1UL, numStates - numStates * MaxMemory / totalUsage);
  klee_warning("killing %lu states (over memory cap: %luMB)", toKill, totalUsage);

  // randomly select states for early termination
  std::vector<ExecutionState *> arr(states.begin(), states.end()); // FIXME: expensive
  for (unsigned i = 0, N = arr.size(); N && i < toKill; ++i, --N) {
    unsigned idx = theRNG.getInt32() % N;
    // Make two pulls to try and not hit a state that
    // covered new code.
    if (arr[idx]->coveredNew)
      idx = theRNG.getInt32() % N;

    std::swap(arr[idx], arr[N - 1]);
    terminateStateEarly(*arr[N - 1], "Memory limit exceeded.", StateTerminationType::OutOfMemory);
  }

  return false;
}

void Executor::doDumpStates() {
  if (!DumpStatesOnHalt || states.empty()) {
    interpreterHandler->incPathsExplored(states.size());
    return;
  }

  klee_message("halting execution, dumping remaining states");
  for (const auto &state : states)
    terminateStateEarly(*state, "Execution halting.", StateTerminationType::Interrupted);
  updateStates(nullptr);
}

void Executor::run(ExecutionState &initialState) {
  bindModuleConstants();

  // Delay init till now so that ticks don't accrue during optimization and such.
  timers.reset();

  states.insert(&initialState);

  if (usingSeeds) {
    std::vector<SeedInfo> &v = seedMap[&initialState];
    
    for (std::vector<KTest*>::const_iterator it = usingSeeds->begin(), 
           ie = usingSeeds->end(); it != ie; ++it)
      v.push_back(SeedInfo(*it));

    int lastNumSeeds = usingSeeds->size()+10;
    time::Point lastTime, startTime = lastTime = time::getWallTime();
    ExecutionState *lastState = 0;
    while (!seedMap.empty()) {
      if (haltExecution) {
        doDumpStates();
        return;
      }

      std::map<ExecutionState*, std::vector<SeedInfo> >::iterator it = 
        seedMap.upper_bound(lastState);
      if (it == seedMap.end())
        it = seedMap.begin();
      lastState = it->first;
      ExecutionState &state = *lastState;
      KInstruction *ki = state.pc;
      stepInstruction(state);

      executeInstruction(state, ki);
      timers.invoke();
      if (::dumpStates) dumpStates();
      if (::dumpPTree) dumpPTree();
      updateStates(&state);

      if ((stats::instructions % 1000) == 0) {
        int numSeeds = 0, numStates = 0;
        for (std::map<ExecutionState*, std::vector<SeedInfo> >::iterator
               it = seedMap.begin(), ie = seedMap.end();
             it != ie; ++it) {
          numSeeds += it->second.size();
          numStates++;
        }
        const auto time = time::getWallTime();
        const time::Span seedTime(SeedTime);
        if (seedTime && time > startTime + seedTime) {
          klee_warning("seed time expired, %d seeds remain over %d states",
                       numSeeds, numStates);
          break;
        } else if (numSeeds<=lastNumSeeds-10 ||
                   time - lastTime >= time::seconds(10)) {
          lastTime = time;
          lastNumSeeds = numSeeds;          
          klee_message("%d seeds remaining over: %d states", 
                       numSeeds, numStates);
        }
      }
    }

    klee_message("seeding done (%d states remain)", (int) states.size());

    if (OnlySeed) {
      doDumpStates();
      return;
    }
  }

  searcher = constructUserSearcher(*this);

  std::vector<ExecutionState *> newStates(states.begin(), states.end());
  searcher->update(0, newStates, std::vector<ExecutionState *>());
  assert(states.size() == 1  && "Unexpected behavior for SyT");
  ExecutionState &state = **states.begin();

  if (AssumeGlobalInvariants) {
    // Assume user-provided system invariants
    assert(state.syt_stage == ASSUME_INVARIANTS);
    std::vector<ref<Expr>> args; // empty, invariants take no arguments.
    for (auto inv : kmodule->sytInvariants) {
      state.invDependencies[inv] = std::set<const MemoryObject *>();
      state.invNamings[inv] = std::vector<std::pair<const MemoryObject *, std::string>>();
      state.invBeingAssumed = inv;

      LOG_STEPS("Assuming invariant: %s", inv->getName().str().c_str());
      ref<Expr> assumption = computeLambda(state, inv, args,
                                          0, 0, 0, LambdaPurpose::CHECK);

      addConstraintGuarded(state, assumption, true, "global inv: " + inv->getName().str());
    }
    state.invBeingAssumed = nullptr;

    for (auto inv : kmodule->sytUncheckedInvariants) {
      ref<Expr> assumption = computeLambda(state, inv, args,
                                          0, 0, 0, LambdaPurpose::CHECK);

      addConstraintGuarded(state, assumption, true, "global inv: " + inv->getName().str());
      LOG_STEPS("Assumed invariant: %s", inv->getName().str().c_str());
    }
  }
  state.syt_stage = EXECUTE_TEST;

  // main interpreter loop
  while (!states.empty() && !haltExecution) {
    ExecutionState &state = searcher->selectState();
    KInstruction *ki = state.pc;
    stepInstruction(state);

    executeInstruction(state, ki);
    timers.invoke();
    if (::dumpStates) dumpStates();
    if (::dumpPTree) dumpPTree();

    updateStates(&state);

    if (!checkMemoryUsage()) {
      // update searchers when states were terminated early due to memory pressure
      updateStates(nullptr);
    }
  }

  delete searcher;
  searcher = nullptr;

  doDumpStates();
}

std::string Executor::getAddressInfo(ExecutionState &state, 
                                     ref<Expr> address) const{
  std::string Str;
  llvm::raw_string_ostream info(Str);
  info << "\taddress: " << address << "\n";
  uint64_t example;
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(address)) {
    example = CE->getZExtValue();
  } else {
    ref<ConstantExpr> value;
    bool success = solver->getValue(state.constraints, address, value,
                                    state.queryMetaData);
    assert(success && "FIXME: Unhandled solver failure");
    (void) success;
    example = value->getZExtValue();
    info << "\texample: " << example << "\n";
    std::pair<ref<Expr>, ref<Expr>> res =
        solver->getRange(state.constraints, address, state.queryMetaData);
    info << "\trange: [" << res.first << ", " << res.second <<"]\n";
  }
  
  MemoryObject hack((unsigned) example);    
  MemoryMap::iterator lower = state.addressSpace.objects.upper_bound(&hack);
  info << "\tnext: ";
  if (lower==state.addressSpace.objects.end()) {
    info << "none\n";
  } else {
    const MemoryObject *mo = lower->first;
    std::string alloc_info;
    mo->getAllocInfo(alloc_info);
    info << "object at " << mo->address
         << " of size " << mo->size << "\n"
         << "\t\t" << alloc_info << "\n";
  }
  if (lower!=state.addressSpace.objects.begin()) {
    --lower;
    info << "\tprev: ";
    if (lower==state.addressSpace.objects.end()) {
      info << "none\n";
    } else {
      const MemoryObject *mo = lower->first;
      std::string alloc_info;
      mo->getAllocInfo(alloc_info);
      info << "object at " << mo->address 
           << " of size " << mo->size << "\n"
           << "\t\t" << alloc_info << "\n";
    }
  }

  return info.str();
}

std::string formatLLVMType(llvm::Type *type, llvm::DataLayout &dataLayout) {
  std::string output;
  llvm::raw_string_ostream ss(output);

  if (type->isArrayTy()) {
    llvm::ArrayType *arrayType = llvm::dyn_cast<llvm::ArrayType>(type);
    llvm::Type *elementType = arrayType->getElementType();
    unsigned numElements = arrayType->getNumElements();
    ss << formatLLVMType(elementType, dataLayout) << "[" << numElements << "]";
  } else if (type->isStructTy()) { 
    llvm::StructType *structType = llvm::dyn_cast<llvm::StructType>(type);
    if (structType->hasName()) {
      ss << structType->getName();
    } else {
      ss << "struct";
    }
  } else if (type->isIntegerTy() || type->isPointerTy() || type->isFloatTy() || type->isDoubleTy()) {
    type->print(ss);
  } else {
    uint64_t size = dataLayout.getTypeAllocSize(type);
    ss << "byte[" << size << "]";
  }

  return ss.str();
}

std::string formatRawBytesCounterExample(const std::vector<unsigned char> &value) {
  std::stringstream ss;
  ss << "[";
  for (size_t i = 0; i < value.size(); ++i) {
    if (i) ss << ", ";
    ss << "0x" << std::hex << std::setw(2) << std::setfill('0')
      << static_cast<int>(value[i]);
  }
  ss << "]";
  return ss.str();
}

std::string formatLLVMValueCounterExample(llvm::Type *type, const std::vector<unsigned char> &bytes, llvm::DataLayout &dataLayout, bool enableTypePrefix = true) {
  std::string output;
  llvm::raw_string_ostream ss(output);

  std::vector<uint64_t> words64;
  size_t num_words64 = (bytes.size() + 7) / 8;
  for (size_t i = 0; i < num_words64; ++i) {
    uint64_t word = 0;
    size_t bytes_to_copy = std::min<size_t>(8, bytes.size() - i * 8);

    std::memcpy(&word, &bytes[i * 8], bytes_to_copy);
    words64.push_back(word);
  }

  if (enableTypePrefix) {
    ss << formatLLVMType(type, dataLayout) << " ";
  }

  if (type->isIntegerTy()) {
    unsigned numBits = type->getIntegerBitWidth();
    llvm::APInt value(numBits, llvm::ArrayRef<uint64_t>(words64.data(), words64.size()));

    value.print(ss, true);
  } else if (type->isPointerTy()) {
    uint64_t pointerSize = dataLayout.getTypeAllocSize(type);
    assert(pointerSize <= 64 && "Pointer size is larger than 64 bits");
    llvm::APInt value(pointerSize, llvm::ArrayRef<uint64_t>(words64.data(), words64.size()));
    uint64_t pointerValue = value.getZExtValue();

    std::stringstream hexss;
    hexss << std::hex << std::setw(pointerSize * 2) << std::setfill('0') << pointerValue;
    ss << "0x" << hexss.str();
  } else if (type->isFloatTy()) {
    assert(bytes.size() == 4 && "Expected 4 bytes for float");
    llvm::APFloat value(llvm::APFloat::IEEEsingle(), llvm::APInt(32, llvm::ArrayRef<uint64_t>(words64.data(), words64.size())));

    value.print(ss);
  } else if (type->isDoubleTy()) {
    assert(bytes.size() == 8 && "Expected 8 bytes for double");
    llvm::APFloat value(llvm::APFloat::IEEEdouble(), llvm::APInt(64, llvm::ArrayRef<uint64_t>(words64.data(), words64.size())));

    value.print(ss);
  } else if (llvm::ArrayType *arrayType = llvm::dyn_cast<llvm::ArrayType>(type)) {
    llvm::Type *elementType = arrayType->getElementType();
    uint64_t elementSize = dataLayout.getTypeAllocSize(elementType);
    unsigned numElements = arrayType->getNumElements();

    ss << "[";
    for (unsigned i = 0; i < numElements; ++i) {
      if (i) ss << ", ";
      std::vector<unsigned char> elementBytes(bytes.begin() + i * elementSize, bytes.begin() + (i + 1) * elementSize);
      ss << formatLLVMValueCounterExample(elementType, elementBytes, dataLayout, false);
    }
    ss << "]";
  } else if (llvm::StructType *structType = llvm::dyn_cast<llvm::StructType>(type)) {
    ss << "{ ";
    uint64_t offset = 0;
    for (unsigned i = 0; i < structType->getNumElements(); ++i) {
      if (i) ss << ", ";
      llvm::Type *elementType = structType->getElementType(i);
      uint64_t elementSize = dataLayout.getTypeAllocSize(elementType);
      std::vector<unsigned char> elementBytes(bytes.begin() + offset, bytes.begin() + offset + elementSize);
      ss << formatLLVMValueCounterExample(elementType, elementBytes, dataLayout);
      offset += elementSize;
    }
    ss << " }";
  } else {
    ss << formatRawBytesCounterExample(bytes);
  }

  return ss.str();
}

std::string formatBVCounterExample(const bitvec_ce_t &value, Expr::Width width) {
  std::string binaryRepr = "0b";
  for (unsigned i = 0; i < width; ++i) {
    unsigned bit_pos = width - i - 1;
    binaryRepr += (value & (1 << bit_pos)) ? "1" : "0";
  }

  std::string typeName = "";
  std::string typeRepr = "";

  switch (width) {
    case Expr::Bool: {
      typeName = "bool";
      typeRepr = value ? "true" : "false";
      break;
    }
    case Expr::Int8: {
      typeName = "i8";
      typeRepr = std::to_string((int8_t) value);
      break;
    }
    case Expr::Int16: {
      typeName = "i16";
      typeRepr = std::to_string((int16_t) value);
      break;
    }
    case Expr::Int32: {
      typeName = "i32";
      typeRepr = std::to_string((int32_t) value);
      break;
    }
    case Expr::Int64: {
      typeName = "i64";
      typeRepr = std::to_string((int64_t) value);
      break;
    }
    case Expr::Fl80: {
      typeName = "f80";
      typeRepr = std::to_string((long double) value);
      break;
    }
    default: {
      typeName = "b" + std::to_string(width);
      typeRepr = binaryRepr;
      break;
    }
  }

  return typeName + " " + typeRepr;
}

std::string formatHeapObjectCounterExample(const std::vector<unsigned char> &value) {
  std::stringstream ss;
  ss << "byte[" << value.size() << "] ";
  ss << formatRawBytesCounterExample(value);
  return ss.str();
}

void Executor::getCounterExample(ExecutionState &state, TimingSolver *solver,
                                const ConstraintSet &constraints, ref<Expr> expr,
                                SolverQueryMetaData &metadata) {
  std::vector<const Array *> arr_objects;
  std::vector<const BitVecExpr *> bv_objects;
  std::vector<const IntExpr *> int_objects;

  std::vector<std::vector<unsigned char>> arr_values;
  std::vector<bitvec_ce_t> bv_values;
  std::vector<int_ce_t> int_values;

  std::vector<bool> arr_values_ok;
  std::vector<bool> bv_values_ok;
  std::vector<bool> int_values_ok;

  std::vector<std::string> arr_c_names;
  std::vector<std::string> bv_c_names;

  std::vector<llvm::Type*> gv_llvm_types;
  std::vector<Expr::Width> bv_widths;

  size_t num_global_vars = 0;

  // tpot_message("Dumping all global variables z3_name -> c_name mapping");
  for (auto it = state.addressSpace.objects.begin(); it != state.addressSpace.objects.end(); ++it) {
    auto mo = it->second->object;
    if (!mo->accessed)
      continue;
    if (mo->name == "unnamed") continue;

    if (mo->allocSite) {
      if (const GlobalValue *gv = dyn_cast<GlobalValue>(mo->allocSite)) {
        const std::string &c_name = gv->getName().str();
        const std::string &z3_name = it->second->updates.root->name;

        // tpot_message("  %s -> %s", z3_name.c_str(), c_name.c_str());
        arr_c_names.push_back(c_name);

        arr_objects.push_back(it->second->updates.root);
        gv_llvm_types.push_back(gv->getValueType());
        num_global_vars++;
      }
    }
  }

  for (auto it = state.symbolic_bitvecs.begin(); it != state.symbolic_bitvecs.end(); ++it) {
    const std::string &z3_name = it->get()->name;
    if(z3_name.rfind("syt_fresh_bv__", 0) == 0) {
      std::string c_name = z3_name.substr(14); 
      c_name = c_name.substr(0, c_name.find("."));

      // tpot_message("  %s -> %s", z3_name.c_str(), c_name.c_str());
      bv_c_names.push_back(c_name);

      bv_objects.push_back(it->get());
      bv_widths.push_back(it->get()->width);
    }
  }

  for (auto it = state.heap.heapObjects.begin(); it != state.heap.heapObjects.end(); ++it) {
    const std::string &z3_name = it->first->name;
    if (!it->first->accessed)
      continue;
    if (z3_name.rfind("obj_at__", 0) == 0) {
      std::string aug_c_name = "object at " + z3_name.substr(8);

      // tpot_message("  %s -> %s", z3_name.c_str(), aug_c_name.c_str());
      arr_c_names.push_back(aug_c_name);

      arr_objects.push_back(it->second->updates.root);
    }
  }

  solver->getCounterExample(constraints, expr, arr_objects, arr_values, arr_values_ok,
                            bv_objects, bv_values, bv_values_ok,
                            int_objects, int_values, int_values_ok,
                            metadata);

  if (arr_values.size() == 0 && bv_values.size() == 0)
    return;
  
  llvm::DataLayout &dataLayout = *kmodule->targetData;

  tpot_message("Counterexample:");
  for (size_t i = 0; i < num_global_vars; ++i) {
    if (!arr_values_ok[i]) {
      tpot_message("  %s: <unassigned>", arr_c_names[i].c_str());
      continue;
    }
    std::string value_str = formatLLVMValueCounterExample(gv_llvm_types[i], arr_values[i], dataLayout);
    tpot_message("  %s: %s", arr_c_names[i].c_str(), value_str.c_str());
  }
  for (size_t i = 0; i < bv_values.size(); ++i) {
    if (!bv_values_ok[i]) {
      tpot_message("  %s: <unassigned>", bv_c_names[i].c_str());
      continue;
    }
    std::string value_str = formatBVCounterExample(bv_values[i], bv_widths[i]);
    tpot_message("  %s: %s", bv_c_names[i].c_str(), value_str.c_str());
  }
  for (size_t i = num_global_vars; i < arr_values.size(); ++i) {
    if (!arr_values_ok[i]) {
      tpot_message("  %s: <unassigned>", arr_c_names[i].c_str());
      continue;
    }
    std::string value_str = formatHeapObjectCounterExample(arr_values[i]);
    tpot_message("  %s: %s", arr_c_names[i].c_str(), value_str.c_str());
  }
}

void Executor::getFailingCodePath(ExecutionState &state) {
  if (!EnableFailingCodePath) return;

  tpot_message("Failing code-path dump:");
  for (auto inst: state.instHistory) {
    tpot_message("  %s | assembly.ll:%d", inst->getSourceLocation().c_str(), inst->info->assemblyLine);
  }
}

void Executor::terminateState(ExecutionState &state) {
  if (replayKTest && replayPosition!=replayKTest->numObjects) {
    klee_warning_once(replayKTest,
                      "replay did not consume all objects in test input.");
  }

  interpreterHandler->incPathsExplored();

  std::vector<ExecutionState *>::iterator it =
      std::find(addedStates.begin(), addedStates.end(), &state);
  if (it==addedStates.end()) {
    state.pc = state.prevPC;

    removedStates.push_back(&state);
  } else {
    // never reached searcher, just delete immediately
    std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it3 = 
      seedMap.find(&state);
    if (it3 != seedMap.end())
      seedMap.erase(it3);
    addedStates.erase(it);
    processTree->remove(state.ptreeNode);
    delete &state;
  }
}

static bool shouldWriteTest(const ExecutionState &state) {
  return !OnlyOutputStatesCoveringNew || state.coveredNew;
}

static std::string terminationTypeFileExtension(StateTerminationType type) {
  std::string ret;
#define TTYPE(N,I,S) case StateTerminationType::N: ret = (S); break;
#define MARK(N,I)
  switch (type) {
  TERMINATION_TYPES
  }
#undef TTYPE
#undef MARK
  return ret;
};

void Executor::terminateStateOnExit(ExecutionState &state, ref<Expr> retVal) {
  if (shouldWriteTest(state) || (AlwaysOutputSeeds && seedMap.count(&state)))
    interpreterHandler->processTestCase(
        state, nullptr,
        terminationTypeFileExtension(StateTerminationType::Exit).c_str());

  
  // Below was only relevant in the context of communicating with py-syt

  // if (sytPostStateSolver) {
  //   // Dump constraints for this path to sytPostStateSolver.
  //   // Later this solver is dumped into an SMTLIB file.

  //   ref<Expr> post_values_constraint = ConstantExpr::alloc(1, Expr::Bool);
  //   ref<Expr> path_condition = ConstantExpr::alloc(1, Expr::Bool);

  //   const Module *m = kmodule->module.get();

  //   for (const GlobalVariable &v : m->globals()) {
  //     if (v.isConstant() || v.isDeclaration()) {
  //       //This excludes constants and external objects.
  //       continue;
  //     }

  //     MemoryObject *mo = globalObjects.find(&v)->second;
  //     const ObjectState *os = state.addressSpace.findObject(mo);

  //     if (os->updates.head) {
  //       // The object has been updated. Communicate this to py-syt.
  //       // It will assume all other objects are not updated.
  //       sytPostStateSolver->addModifiedField(v.getName().str());
  //     } else {
  //       continue;
  //     }

  //     // create symbolic array
  //     auto name = "syt_postval__" + v.getName().str();
  //     const Array *array = arrayCache.CreateArray(name, mo->size);

  //     //! Passing the updatelist by reference is not memory safe...
  //     post_values_constraint = AndExpr::create(
  //         post_values_constraint, ArrayEqExpr::create(os->updates, UpdateList(array, 0)));


  //     // for (int i = 0; i < mo->size; i++) {
  //     //   ref<Expr> value = os->read(i, Expr::Int8);
  //     //   ref<Expr> post_value = ReadExpr::create(UpdateList(array, 0), ConstantExpr::alloc(i, Expr::Int32));
  //     //   post_values_constraint = AndExpr::create(
  //     //     post_values_constraint, EqExpr::create(value, post_value));
  //     // }
  //   }

  //   for (auto &constraint : state.constraints) {
  //     path_condition = AndExpr::create(path_condition, constraint);
  //   }

  //   // the 4-byte retval size is tailored for hyperkernel, where syscalls return ints.
  //   assert(retVal->getWidth() == Expr::Int32 && "retval is not 4 bytes");
  //   auto sytRetVal = BitVecExpr::create("syt_retval", Expr::Int32);

  //   // path condition implies post_values_constraint, and syt_retval == retVal
  //   sytPostStateSolver->addConstraint(
  //     OrExpr::create(Expr::createIsZero(path_condition),
  //       AndExpr::create(post_values_constraint,
  //         EqExpr::create(retVal, sytRetVal))
  //       )
  //   );
  // }

  assert(state.syt_stage == EXECUTE_TEST);
  state.syt_stage = ASSERT_INVARIANTS;
  state.heap.namesToObjects.clear();
  //tmp
  state.heap.has_unnamed_shortcut = true;

  if (AssertGlobalInvariants && !state.skipInvariantChecks) {
    std::vector<ref<Expr>> args; // empty, invariants take no arguments.

    for (auto inv : kmodule->sytInvariants) {
      // see if this specific invariant can be skipped
      std::set<const MemoryObject *> dependencies = state.invDependencies[inv];
      bool skip = true;
      for (const MemoryObject *dep : dependencies) {
        if(state.modifiedGlobals.find(dep) != state.modifiedGlobals.end())
        skip = false;
      }

      if (!AssumeGlobalInvariants)
        skip = false;

      if (skip) {
        LOG_STEPS("Skipping invariant that trivially holds: %s", inv->getName().str().c_str());
        // emulate the naming effects of executing the invariant.
        std::vector<std::pair<const MemoryObject *, std::string>> namings = state.invNamings[inv];
        for (const auto &it : namings) {
          auto obj = it.first;
          auto name = it.second;
          bool namingSuccess = state.heap.getWriteable(obj, state.heap.findObject(obj))->name(name);
          if (!namingSuccess) {
            terminateStateOnUserError(
              state, "Invariant does not hold due to naming" + inv->getName().str());
          }
        }
        continue;
      } else {
        LOG_STEPS("Checking invariant: %s", inv->getName().str().c_str());
        bool success = lambdaMustReturnTrue(state, inv, args, /*nameParentsObjects* = */true);
        if (!success) {
          terminateStateOnUserError(
              state, "Invariant does not hold " + inv->getName().str());
          return;
        } else {
          LOG_STEPS("Invariant holds: %s", inv->getName().str().c_str());
        }
      }
    }
  } else {
    assert(0);  // should not reach here
    LOG_STEPS("Skipping invariant checks (unsoundly)");
  }

  checkForLeaks(state);

  interpreterHandler->incPathsCompleted();
  terminateState(state);
}

void Executor::terminateStateEarly(ExecutionState &state, const Twine &message,
                                   StateTerminationType terminationType) {
  if ((terminationType <= StateTerminationType::EXECERR &&
       shouldWriteTest(state)) ||
      (AlwaysOutputSeeds && seedMap.count(&state))) {
    interpreterHandler->processTestCase(
        state, (message + "\n").str().c_str(),
        terminationTypeFileExtension(terminationType).c_str());
  }

  terminateState(state);
}

void Executor::terminateStateOnUserError(ExecutionState &state, const llvm::Twine &message) {
  terminateStateOnError(state, message, StateTerminationType::User, "");
}

const InstructionInfo & Executor::getLastNonKleeInternalInstruction(const ExecutionState &state,
    Instruction ** lastInstruction) {
  // unroll the stack of the applications state and find
  // the last instruction which is not inside a KLEE internal function
  ExecutionState::stack_ty::const_reverse_iterator it = state.stack.rbegin(),
      itE = state.stack.rend();

  // don't check beyond the outermost function (i.e. main())
  itE--;

  const InstructionInfo * ii = 0;
  if (kmodule->internalFunctions.count(it->kf->function) == 0){
    ii =  state.prevPC->info;
    *lastInstruction = state.prevPC->inst;
    //  Cannot return yet because even though
    //  it->function is not an internal function it might of
    //  been called from an internal function.
  }

  // Wind up the stack and check if we are in a KLEE internal function.
  // We visit the entire stack because we want to return a CallInstruction
  // that was not reached via any KLEE internal functions.
  for (;it != itE; ++it) {
    // check calling instruction and if it is contained in a KLEE internal function
    const Function * f = (*it->caller).inst->getParent()->getParent();
    if (kmodule->internalFunctions.count(f)){
      ii = 0;
      continue;
    }
    if (!ii){
      ii = (*it->caller).info;
      *lastInstruction = (*it->caller).inst;
    }
  }

  if (!ii) {
    // something went wrong, play safe and return the current instruction info
    *lastInstruction = state.prevPC->inst;
    return *state.prevPC->info;
  }
  return *ii;
}

bool shouldExitOn(StateTerminationType reason) {
  auto it = std::find(ExitOnErrorType.begin(), ExitOnErrorType.end(), reason);
  return it != ExitOnErrorType.end();
}

void Executor::terminateStateOnError(ExecutionState &state,
                                     const llvm::Twine &messaget,
                                     StateTerminationType terminationType,
                                     const llvm::Twine &info,
                                     const char *suffix) {
  std::string message = messaget.str();
  static std::set< std::pair<Instruction*, std::string> > emittedErrors;
  Instruction * lastInst;
  const InstructionInfo &ii = getLastNonKleeInternalInstruction(state, &lastInst);

  if (EmitAllErrors ||
      emittedErrors.insert(std::make_pair(lastInst, message)).second) {
    if (!ii.file.empty()) {
      klee_message("ERROR: %s:%d: %s", ii.file.c_str(), ii.line, message.c_str());
    } else {
      klee_message("ERROR: (location information missing) %s", message.c_str());
    }
    if (!EmitAllErrors)
      klee_message("NOTE: now ignoring this error at this location");

    std::string MsgString;
    llvm::raw_string_ostream msg(MsgString);
    msg << "Error: " << message << '\n';
    if (!ii.file.empty()) {
      msg << "File: " << ii.file << '\n'
          << "Line: " << ii.line << '\n'
          << "assembly.ll line: " << ii.assemblyLine << '\n'
          << "State: " << state.getID() << '\n';
    }
    msg << "Stack: \n";
    state.dumpStack(msg);

    std::string info_str = info.str();
    if (!info_str.empty())
      msg << "Info: \n" << info_str;

    const std::string ext = terminationTypeFileExtension(terminationType);
    // use user provided suffix from klee_report_error()
    const char * file_suffix = suffix ? suffix : ext.c_str();
    interpreterHandler->processTestCase(state, msg.str().c_str(), file_suffix);
  }
#ifndef NDEBUG
  raise(SIGINT);
#endif

  interpreterHandler->incErrorPaths();
  terminateState(state);

  if (shouldExitOn(terminationType))
    haltExecution = true;
}

void Executor::terminateStateOnExecError(ExecutionState &state,
                                         const llvm::Twine &message,
                                         const llvm::Twine &info) {
  terminateStateOnError(state, message, StateTerminationType::Execution, info);
}

void Executor::terminateStateOnSolverError(ExecutionState &state,
                                           const llvm::Twine &message) {
  terminateStateOnError(state, message, StateTerminationType::Solver, "");
}

// XXX shoot me
static const char *okExternalsList[] = { "printf", 
                                         "fprintf", 
                                         "puts",
                                         "getpid" };
static std::set<std::string> okExternals(okExternalsList,
                                         okExternalsList + 
                                         (sizeof(okExternalsList)/sizeof(okExternalsList[0])));

void Executor::callExternalFunction(ExecutionState &state,
                                    KInstruction *target,
                                    Function *function,
                                    std::vector< ref<Expr> > &arguments) {
  // check if specialFunctionHandler wants it
  if (specialFunctionHandler->handle(state, function, target, arguments))
    return;

  if (ExternalCalls == ExternalCallPolicy::None &&
      !okExternals.count(function->getName().str())) {
    klee_warning("Disallowed call to external function: %s\n",
               function->getName().str().c_str());
    terminateStateOnUserError(state, "external calls disallowed");
    return;
  }

  // normal external function handling path
  // allocate 128 bits for each argument (+return value) to support fp80's;
  // we could iterate through all the arguments first and determine the exact
  // size we need, but this is faster, and the memory usage isn't significant.
  uint64_t *args = (uint64_t*) alloca(2*sizeof(*args) * (arguments.size() + 1));
  memset(args, 0, 2 * sizeof(*args) * (arguments.size() + 1));
  unsigned wordIndex = 2;
  for (std::vector<ref<Expr> >::iterator ai = arguments.begin(), 
       ae = arguments.end(); ai!=ae; ++ai) {
    if (ExternalCalls == ExternalCallPolicy::All) { // don't bother checking uniqueness
      *ai = optimizer.optimizeExpr(*ai, true);
      ref<ConstantExpr> ce;
      bool success =
          solver->getValue(state.constraints, *ai, ce, state.queryMetaData);
      if (!success && isSmokeTest) {
        terminateState(state);
        return;
      }
      assert(success && "FIXME: Unhandled solver failure");
      (void) success;
      ce->toMemory(&args[wordIndex]);
      ObjectPair op;
      // Checking to see if the argument is a pointer to something
      if (ce->getWidth() == Context::get().getPointerWidth() &&
          state.addressSpace.resolveOne(ce, op)) {
        op.second->flushToConcreteStore(solver, state);
      }
      wordIndex += (ce->getWidth()+63)/64;
    } else {
      ref<Expr> arg = toUnique(state, *ai);
      if (ConstantExpr *ce = dyn_cast<ConstantExpr>(arg)) {
        // fp80 must be aligned to 16 according to the System V AMD 64 ABI
        if (ce->getWidth() == Expr::Fl80 && wordIndex & 0x01)
          wordIndex++;

        // XXX kick toMemory functions from here
        ce->toMemory(&args[wordIndex]);
        wordIndex += (ce->getWidth()+63)/64;
      } else {
        terminateStateOnExecError(state,
                                  "external call with symbolic argument: " +
                                  function->getName());
        return;
      }
    }
  }

  // Prepare external memory for invoking the function
  state.addressSpace.copyOutConcretes();
#ifndef WINDOWS
  // Update external errno state with local state value
  int *errno_addr = getErrnoLocation(state);
  ObjectPair result;
  bool resolved = state.addressSpace.resolveOne(
      ConstantExpr::create((uint64_t)errno_addr, Expr::Int64), result);
  if (!resolved)
    klee_error("Could not resolve memory object for errno");
  ref<Expr> errValueExpr = result.second->read(0, sizeof(*errno_addr) * 8, false);
  ConstantExpr *errnoValue = dyn_cast<ConstantExpr>(errValueExpr);
  if (!errnoValue) {
    terminateStateOnExecError(state,
                              "external call with errno value symbolic: " +
                                  function->getName());
    return;
  }

  externalDispatcher->setLastErrno(
      errnoValue->getZExtValue(sizeof(*errno_addr) * 8));
#endif

  if (!SuppressExternalWarnings) {

    std::string TmpStr;
    llvm::raw_string_ostream os(TmpStr);
    os << "calling external: " << function->getName().str() << "(";
    for (unsigned i=0; i<arguments.size(); i++) {
      os << arguments[i];
      if (i != arguments.size()-1)
        os << ", ";
    }
    os << ") at " << state.pc->getSourceLocation();
    
    if (AllExternalWarnings)
      klee_warning("%s", os.str().c_str());
    else
      klee_warning_once(function, "%s", os.str().c_str());
  }

  bool success = externalDispatcher->executeCall(function, target->inst, args);
  if (!success) {
    terminateStateOnError(state, "failed external call: " + function->getName(),
                          StateTerminationType::External);
    return;
  }

  if (!state.addressSpace.copyInConcretes()) {
    terminateStateOnError(state, "external modified read-only object",
                          StateTerminationType::External);
    return;
  }

#ifndef WINDOWS
  // Update errno memory object with the errno value from the call
  int error = externalDispatcher->getLastErrno();
  state.addressSpace.copyInConcrete(result.first, result.second,
                                    (uint64_t)&error);
#endif

  Type *resultType = target->inst->getType();
  if (resultType != Type::getVoidTy(function->getContext())) {
    ref<Expr> e = ConstantExpr::fromMemory((void*) args, 
                                           getWidthForLLVMType(resultType));
    bindLocal(target, state, e);
  }
}

/***/

void Executor::updateNonNullConstraint(ref<Expr> *non_null_constr, const ref<Expr> &path_result) {
    if (non_null_constr == NULL)
      return;

    ConstantExpr *CE = dyn_cast<ConstantExpr>(path_result);
    if (CE) 
      return;

    // Account for a compiler optimization merging paths
    SelectExpr *SE = dyn_cast<SelectExpr>(path_result);
    if (SE) {
      updateNonNullConstraint(non_null_constr, SE->trueExpr);
      updateNonNullConstraint(non_null_constr, SE->falseExpr);
      return;
    }

    *non_null_constr = AndExpr::create(
        NotExpr::create(
          EqExpr::create(ConstantExpr::create(0, Context::get().getPointerWidth()),
          path_result)), *non_null_constr);
}

// copied from Constraints.cpp -- helper for computeLambdaMemoized
class ExprReplaceVisitor : public ExprVisitor {
private:
  ref<Expr> src, dst;

public:
  ExprReplaceVisitor(const ref<Expr> &_src, const ref<Expr> &_dst)
      : src(_src), dst(_dst) {}

  Action visitExpr(const Expr &e) override {
    if (e == *src) {
      return Action::changeTo(dst);
    }
    return Action::doChildren();
  }

  Action visitExprPost(const Expr &e) override {
    if (e == *src) {
      return Action::changeTo(dst);
    }
    return Action::doChildren();
  }
};

class ReadReplaceVisitor : public ExprVisitor {
private:
  const ObjectState *src, *dst;

public:
  ReadReplaceVisitor(const ObjectState *_src, const ObjectState *_dst)
      : src(_src), dst(_dst) {
      assert(!src->updates.head && "updates on dummy array");
      assert(!dst->updates.head && "updates on actual array");

  }

  Action visitRead(const ReadExpr &e) override {
    if (e.updates.root == src->updates.root) {
      assert(!e.updates.head && "updates on dummy array");
      
      // this is a read from the dummy object. Replace with read from actual object.
      return Action::changeTo(ReadExpr::create(dst->updates, e.index));
    }
    return Action::doChildren();
  }
};

ref<Expr> Executor::computeLambdaMemoized(ExecutionState &state, llvm::Function *f,
                   std::vector<ref<Expr> > &arguments, ref<Expr> *non_null_constr, const ObjectState *actualObject) {
  assert(lambdaMemos.count(f) > 0);
  assert(arguments.size() == f->arg_size());

  const ObjectState *dummyObject = lambdaMemos[f].dummyObject;
  ref<Expr> res = lambdaMemos[f].result;
  ref<Expr> res_nonnull = lambdaMemos[f].non_null_constr;

  for (int i = 0; i < arguments.size(); i++) {
    ref<Expr> mem_arg = lambdaMemos[f].arguments[i];
    assert(mem_arg->getWidth() == arguments[i]->getWidth());

    // We need to replace the argument with the actual value.
    ExprReplaceVisitor visitor(mem_arg, arguments[i]);

    res = visitor.visit(res);

    if (non_null_constr) {
      res_nonnull = visitor.visit(res_nonnull);
    }

    // -- We also need to replace reads if a dummy object has been used -- //
    assert((dummyObject == NULL) == (actualObject == NULL));
    if (dummyObject) {
      // the lambda is known over the initial version of the actual object, 
      // not an updated version.
      const ObjectState *actualObjectInit = actualObject;
      if (actualObject->updates.head) {
        actualObjectInit = new ObjectState(actualObject->object.get(), actualObject->updates.root);
      }
      
      ReadReplaceVisitor readVisitor(dummyObject, actualObjectInit);
      res = readVisitor.visit(res);
      if (non_null_constr) {
        res_nonnull = visitor.visit(res_nonnull);
      }

      if (actualObjectInit != actualObject) {
        delete actualObjectInit;
      }

      // replace the dummy object's base address, too.
      auto *dummySS = dynamic_cast<const SytSSMemoryObject *>(dummyObject->object.get());
      assert(dummySS);
      ref<Expr> dummyBase = dummySS->uniqueHeapAddress;
      assert(dummyBase->getKind() == Expr::BitVec || 
             dummyBase->getKind() == Expr::BV2Int && 
             dummyBase->getKid(0)->getKind() == Expr::BitVec); // dummy object addresses are fresh bitvecs
      auto *actualSS = dynamic_cast<const SytSSMemoryObject *>(actualObject->object.get());
      ExprReplaceVisitor baseVisitor(dummyBase, actualSS->uniqueHeapAddress);
      res = baseVisitor.visit(res);
      if (non_null_constr) {
        res_nonnull = baseVisitor.visit(res_nonnull);
      }

      // and the base's bitvector version.. just in case
      ref<Expr> dummyBaseBV = BV2IntExpr::getBVForm(dummySS->uniqueHeapAddress);
      ref<Expr> actualBaseBV = BV2IntExpr::getBVForm(actualSS->uniqueHeapAddress);
      ExprReplaceVisitor baseBVVisitor(dummyBaseBV, actualBaseBV);
      res = baseBVVisitor.visit(res);
      if (non_null_constr) {
        res_nonnull = baseBVVisitor.visit(res_nonnull);
      }
    }
  }

  // The replacement may have created ill-formed BV2Int expressions.
  // Replace them with properly constructed versions here.
  
    for (int i = 0; i < arguments.size(); i++) {
      // skip arguments that can't be bv2int atoms
      if (arguments[i]->getWidth() == 64) {

        ExprReplaceVisitor visitor(BV2IntExpr::create(arguments[i]), 
          convertToInteger(state,arguments[i]));

        res = visitor.visit(res);
        if (non_null_constr) {
          res_nonnull = visitor.visit(res_nonnull);
        } 
      }
    }

  // It may also have skipped some simplifications and axiom instantiations.
  res = doTpotSimplifications(state, res);
  if (non_null_constr) {
    res_nonnull = doTpotSimplifications(state, res_nonnull);
  }



  if (non_null_constr) {
    *non_null_constr = res_nonnull;
  }
  return res;
}


ref<Expr> Executor::computeLambda(ExecutionState &state, llvm::Function *f,
                   std::vector<ref<Expr> > &arguments, ref<Expr> *non_null_constr, MemoryObject *dummyObject,
                   bool *mustReturnTrue, LambdaPurpose purpose, bool nameParentsObjects) {
  // assert(state.syt_stage != EXECUTE_TEST);

  // Short path: if computing over the initial state, we can use the memoized results.
  if (state.syt_stage == ASSUME_INVARIANTS && lambdaMemos.count(f) > 0 && purpose == MEMOIZE) {
    if (purpose == MEMOIZE || purpose == INSTANTIATE) {
      return computeLambdaMemoized(state, f, arguments, non_null_constr, dummyObject ? state.heap.findObject(dummyObject): NULL);
    }
  }

  //! Very likely, we needed these to identify fzoneResPath while executing the lambda.
  //! We should do that through other means. While re-establishing an invariant, we don't want to
  //! override the lambda memo.
  //  [dummy object logic]
  // if (/*state.syt_stage == ASSUME_INVARIANTS && */purpose == MEMOIZE) { 
  //   struct LambdaMemo memo;
  //   memo.dummyObject = dummyObject ? state.heap.findObject(dummyObject): NULL;
  //   memo.fzoneResPath = NULL;
  //   memo.candidateObject = dummyObject;
  //   lambdaMemos[f] = memo;
  // }  

  if (non_null_constr)
    *non_null_constr = ConstantExpr::alloc(1, Expr::Bool);

  if (mustReturnTrue) {
    assert(getWidthForLLVMType(f->getReturnType()) == Expr::Bool);
    *mustReturnTrue = true;
  }

  // We save the added states and restore them after the lambda is computed.
  std::vector<ExecutionState *> original_addedStates = addedStates;
  lambdaParentAddedStates.push_back(original_addedStates);
  addedStates.clear();

  if (llvm::isa<llvm::InlineAsm>(f)) {
    terminateStateOnExecError(state, "inline assembly is unsupported");
  }
  
  // Create another state to compute the lambda.
  // Otherwise we add constraints from the returning lambda path to the current state. 
  auto lambda_state = state.branch();
  lambda_state->lambdaPathConstraints.push_back(std::vector<ref<Expr>>());
  lambda_state->lambdaParent = &state;
  /* this is a dirty solution that allows invariants to claim objects before the leak check*/
  lambda_state->nameParentsObjects = nameParentsObjects;
  lambda_state->lambdaPurpose = purpose;
  lambda_state->lambdaFunction = f;
  addedStates.push_back(lambda_state);
  processTree->attach(state.ptreeNode, lambda_state, &state, BranchType::SytComputeLambda);

  // This will push the handleSytAssumeForall call onto the stack as the
  // call to the lambda is never actually made in the source.
  executeCall(*lambda_state, &*(lambda_state->prevPC), f, arguments);

  // used if the lambda returns a boolean
  std::vector<ref<Expr> > path_result_constraints;
  // used if lambda returns a bit vector
  ref<Expr> path_result_ite = NULL;

  ExecutionState *curState = lambda_state;
  std::size_t i = 0;
  std::size_t init_stack_size = curState->stack.size();
  while (true) {
    while (true) {
      KInstruction *ki = curState->pc;
      // Let's allow calls and track stack size..
      if (ki->inst->getOpcode() == Instruction::Ret) {
        if (curState->stack.size() == init_stack_size) {
          break;
        }
      }
      stepInstruction(*curState);

      auto prev_sz = addedStates.size();
      executeInstruction(*curState, ki);

      if (addedStates.size() > prev_sz) {
        // assert(ki->inst->getOpcode() == Instruction::Br);
      }
    }

    // handle the return instruction.
    // we don't "step" over the return instruction, so look at pc, not prevPC.
    assert(curState->pc->inst->getFunction() == f && "Something is wrong, probably re: addedStates");
    LOG_STEPS_VERBOSE("Lambda path finished (%s)", f->getName().str().c_str());
    KInstruction *ki = curState->pc;
    ReturnInst *ri = cast<ReturnInst>(ki->inst);
    // KInstIterator kcaller = curState->stack.back().caller;
    if (ri->getNumOperands() == 0) {
      klee_error("Lambda function returns void");
    }
    ref<Expr> path_result = eval(ki, 0, *curState).value;

    if (mustReturnTrue) {
      ConstantExpr *CE = dyn_cast<ConstantExpr>(path_result);
      if (CE) {
        assert(CE->getWidth() == Expr::Bool);
        if (!CE->isTrue()) {
          // raise(SIGINT);
          getFailingCodePath(*curState);
          *mustReturnTrue = false;
          goto cleanup;
        }
      } else {
        // Does the path constraint make the value true?
        std::vector<ref<Expr>> unsignedExprs;
        ref<Expr> b2ic =
            BV2IntExpr::convertConstraint(path_result, unsignedExprs);
        ref<Expr> unsignedConstrs =
            curState->getUnsignedConstraints(unsignedExprs);

        ConstraintSet constraints;
        constraints = curState->getConstraints(true);
        std::vector<ref<BV2IntExpr>> tpot_bv2int_exprs;

        bool res;
        bool success __attribute__((unused));
        success = solver->mustBeTrue(constraints, path_result, res,
                                     curState->queryMetaData);
        if (!res) {
          getCounterExample(*curState, solver, curState->getConstraints(/*useHeapConstraints=*/true),
                            path_result, curState->queryMetaData);
          getFailingCodePath(*curState);
          // raise(SIGINT);
          *mustReturnTrue = false;
          goto cleanup;
        }

      }
    }
    updateNonNullConstraint(non_null_constr, path_result);

    // if (path_result->getWidth() == Expr::Bool)
    //   path_result = NeExpr::create(path_result, ConstantExpr::create(0, path_result->getWidth()));

    ref<Expr> path_condition = getLambdaPathCondition(*curState);

    if (getWidthForLLVMType(f->getReturnType()) == Expr::Bool)
      path_result_constraints.push_back(AndExpr::create(path_condition, path_result));
    else {
      if (path_result_ite.isNull()) {
        // We default to the first result if no path condition is met. 
        // This should be safe as long as the discjunction of all path conditions covers all possibilities.
        path_result_ite = path_result;
      } else {
        path_result_ite = SelectExpr::create(path_condition, path_result, path_result_ite);
      }
    }

//#define LAMBDA_BREADTH_FIRST
#ifdef LAMBDA_BREADTH_FIRST
    i++;
    if (i < addedStates.size()) {
      curState = addedStates[i];
    }
    else
      break;
#else
    auto it = std::find(addedStates.begin(), addedStates.end(), curState);
    assert(it != addedStates.end() && "invalid state termiated");
    addedStates.erase(it);
    delete curState;
    if (addedStates.size() > 0) {
      curState = addedStates.back();
    } else {
      break;
    }

#endif

  }

cleanup:
  // Deallocate all states in addedStates.
  for (auto s : addedStates) {
    delete s;
  }

  addedStates.clear();
  addedStates = original_addedStates;
  lambdaParentAddedStates.pop_back();

  if (mustReturnTrue) {
    // we are not interested in the return value.
    return NULL;
  }

  ref<Expr> ret;
  // Special case for when the return value of a lambda is boolean.
  if (getWidthForLLVMType(f->getReturnType()) == Expr::Bool) {
    ref<Expr> bool_result = path_result_constraints[0];
    for (unsigned i = 1; i < path_result_constraints.size(); i++) {
      // std::vector<ref<Expr>> unsignedExprs;
      // ref<Expr> b2ic =
      //     BV2IntExpr::convertConstraint(path_result_constraints[i],
      //     unsignedExprs);
      // ref<Expr> unsignedConstrs =
      //     curState->getUnsignedConstraints(unsignedExprs);
      // ref<Expr> condAug = AndExpr::create(
      //     path_result_constraints[i], AndExpr::create(b2ic,
      //     unsignedConstrs));

      // bool_result = OrExpr::create(bool_result, condAug);
      bool_result = OrExpr::create(bool_result, path_result_constraints[i]);
    }

    ret = bool_result;

    // std::vector<ref<Expr>> unsignedExprs;
    // ref<Expr> b2ic =
    //     BV2IntExpr::convertConstraint(bool_result, unsignedExprs);
    // ref<Expr> unsignedConstrs =
    //     curState->getUnsignedConstraints(unsignedExprs);
    // ref<Expr> condAug = AndExpr::create(
    //     bool_result, AndExpr::create(b2ic, unsignedConstrs));
    // ret = condAug;
  } else {
    ret = path_result_ite;
  }

  // Memoize the return value if the lambda was executed over the inital state.
  if (purpose == MEMOIZE) {
    struct LambdaMemo memo;
    lambdaMemos[f] = memo;
    lambdaMemos[f].arguments = arguments;
    lambdaMemos[f].non_null_constr = non_null_constr ? *non_null_constr : NULL;
    lambdaMemos[f].result = ret;
    lambdaMemos[f].dummyObject = dummyObject ? state.heap.findObject(dummyObject): NULL;
    lambdaMemos[f].fzoneResPath = NULL;
    lambdaMemos[f].candidateObject = dummyObject;
  }

  return ret;
}

ref<Expr> Executor::getLambdaPathCondition(ExecutionState &state) {
  assert(state.lambdaParent && "This is not a lambda state");
  assert(state.lambdaPathConstraints.size() > 0);

  ref<Expr> res = ConstantExpr::alloc(1, Expr::Bool);
  for (auto &constraint : state.lambdaPathConstraints.back()) {
    res = AndExpr::create(res, constraint);
  }
  return res;
}

bool Executor::lambdaMustReturnTrue(ExecutionState &state, llvm::Function *f,
                std::vector<ref<Expr> > &arguments,  bool nameParentsObjects) {
  bool res;
  computeLambda(state, f, arguments, NULL, NULL, &res, /*purpose=*/CHECK, nameParentsObjects);
  return res;
}


/***/

ref<Expr> Executor::replaceReadWithSymbolic(ExecutionState &state, 
                                            ref<Expr> e) {
  unsigned n = interpreterOpts.MakeConcreteSymbolic;
  if (!n || replayKTest || replayPath)
    return e;

  // right now, we don't replace symbolics (is there any reason to?)
  if (!isa<ConstantExpr>(e))
    return e;

  if (n != 1 && random() % n)
    return e;

  // create a new fresh location, assert it is equal to concrete value in e
  // and return it.
  
  static unsigned id;
  const Array *array =
      arrayCache.CreateArray("rrws_arr" + llvm::utostr(++id),
                             Expr::getMinBytesForWidth(e->getWidth()));
  ref<Expr> res = Expr::createTempRead(array, e->getWidth());
  ref<Expr> eq = NotOptimizedExpr::create(EqExpr::create(e, res));
  llvm::errs() << "Making symbolic: " << eq << "\n";
  state.addConstraint(eq);
  return res;
}

ObjectState *Executor::bindObjectInState(ExecutionState &state, 
                                         const MemoryObject *mo,
                                         bool isLocal,
                                         const Array *array) {
  ObjectState *os;

  const SytSSMemoryObject *smo = dynamic_cast<const SytSSMemoryObject *>(mo);
  if (smo) {
    assert(array && "Expected array");
    const ForallZone *fz = dynamic_cast<const ForallZone *>(mo);
    if (fz) {
      os = new SytFZoneObjectState(smo, array);
    } else {
      os = new SytSSObjectState(smo, array);
    }
  } else {
    // If the object is an initial value in the global state corresponding to an integer or a pointer,
    // try using the bitvec representaiton. Doing this for arrays or structs may result in bitwidth
    // mismatches on read/write.
    bool skipBVRepr = !mo->allocSite || (mo->allocSite->getType()->isPointerTy() || mo->allocSite->getType()->isIntegerTy());
    if (!skipBVRepr && mo->isGlobal) {
      // LLVM represents global arrays using pointer
      auto ptrTy = dyn_cast<PointerType>(mo->allocSite->getType());
      if (ptrTy) {
        auto pointeeTy = ptrTy->getElementType();
        if (pointeeTy && (!pointeeTy->isPointerTy() && !pointeeTy->isIntegerTy())) {
          skipBVRepr = true;
        }
      }
    }


    bool useBVRepr = !skipBVRepr && (mo->name.rfind("syt_initval__", 0) == 0);
    os = array ? new ObjectState(mo, array, useBVRepr) : new ObjectState(mo);
  }

  if (mo->uniqueHeapAddress) {
    state.heap.bindObject(mo, os);
  }
  else
    state.addressSpace.bindObject(mo, os);

  // Its possible that multiple bindings of the same mo in the state
  // will put multiple copies on this list, but it doesn't really
  // matter because all we use this list for is to unbind the object
  // on function return.
  if (isLocal)
    state.stack.back().allocas.push_back(mo);

  return os;
}

void Executor::executeAlloc(ExecutionState &state,
                            ref<Expr> size,
                            bool isLocal,
                            KInstruction *target,
                            bool zeroMemory,
                            const ObjectState *reallocFrom,
                            size_t allocationAlignment) {
  size = toUnique(state, size);
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(size)) {
    const llvm::Value *allocSite = state.prevPC->inst;
    if (allocationAlignment == 0) {
      allocationAlignment = getAllocationAlignment(allocSite);
    }
    MemoryObject *mo =
        memory->allocate(CE->getZExtValue(), isLocal, /*isGlobal=*/false,
                         allocSite, allocationAlignment);
    if (!mo) {
      bindLocal(target, state, 
                ConstantExpr::alloc(0, Context::get().getPointerWidth()));
    } else {
      ObjectState *os = bindObjectInState(state, mo, isLocal);
      if (zeroMemory) {
        os->initializeToZero();
      } else {
        os->initializeToRandom();
      }
      bindLocal(target, state, mo->getBaseExpr());
      
      if (reallocFrom) {
        unsigned count = std::min(reallocFrom->size, os->size);
        for (unsigned i=0; i<count; i++)
          os->write(i, reallocFrom->read8(i, false));
        state.addressSpace.unbindObject(reallocFrom->getObject());
      }
    }
  } else {
    // XXX For now we just pick a size. Ideally we would support
    // symbolic sizes fully but even if we don't it would be better to
    // "smartly" pick a value, for example we could fork and pick the
    // min and max values and perhaps some intermediate (reasonable
    // value).
    // 
    // It would also be nice to recognize the case when size has
    // exactly two values and just fork (but we need to get rid of
    // return argument first). This shows up in pcre when llvm
    // collapses the size expression with a select.

    size = optimizer.optimizeExpr(size, true);

    ref<ConstantExpr> example;
    bool success =
        solver->getValue(state.constraints, size, example, state.queryMetaData);
    assert(success && "FIXME: Unhandled solver failure");
    (void) success;
    
    // Try and start with a small example.
    Expr::Width W = example->getWidth();
    while (example->Ugt(ConstantExpr::alloc(128, W))->isTrue()) {
      ref<ConstantExpr> tmp = example->LShr(ConstantExpr::alloc(1, W));
      bool res;
      bool success =
          solver->mayBeTrue(state.constraints, EqExpr::create(tmp, size), res,
                            state.queryMetaData);
      assert(success && "FIXME: Unhandled solver failure");      
      (void) success;
      if (!res)
        break;
      example = tmp;
    }

    StatePair fixedSize =
        fork(state, EqExpr::create(example, size), true, BranchType::Alloc);

    if (fixedSize.second) { 
      // Check for exactly two values
      ref<ConstantExpr> tmp;
      bool success = solver->getValue(fixedSize.second->constraints, size, tmp,
                                      fixedSize.second->queryMetaData);
      assert(success && "FIXME: Unhandled solver failure");      
      (void) success;
      bool res;
      success = solver->mustBeTrue(fixedSize.second->constraints,
                                   EqExpr::create(tmp, size), res,
                                   fixedSize.second->queryMetaData);
      assert(success && "FIXME: Unhandled solver failure");      
      (void) success;
      if (res) {
        executeAlloc(*fixedSize.second, tmp, isLocal,
                     target, zeroMemory, reallocFrom);
      } else {
        // See if a *really* big value is possible. If so assume
        // malloc will fail for it, so lets fork and return 0.
        StatePair hugeSize =
            fork(*fixedSize.second,
                 UltExpr::create(ConstantExpr::alloc(1U << 31, W), size), true,
                 BranchType::Alloc);
        if (hugeSize.first) {
          klee_message("NOTE: found huge malloc, returning 0");
          bindLocal(target, *hugeSize.first, 
                    ConstantExpr::alloc(0, Context::get().getPointerWidth()));
        }
        
        if (hugeSize.second) {

          std::string Str;
          llvm::raw_string_ostream info(Str);
          ExprPPrinter::printOne(info, "  size expr", size);
          info << "  concretization : " << example << "\n";
          info << "  unbound example: " << tmp << "\n";
          terminateStateOnError(*hugeSize.second, "concretized symbolic size",
                                StateTerminationType::Model, info.str());
        }
      }
    }

    if (fixedSize.first) // can be zero when fork fails
      executeAlloc(*fixedSize.first, example, isLocal, 
                   target, zeroMemory, reallocFrom);
  }
}

void Executor::executeFree(ExecutionState &state,
                           ref<Expr> address,
                           KInstruction *target) {
  address = optimizer.optimizeExpr(address, true);
  StatePair zeroPointer =
      fork(state, Expr::createIsZero(address), true, BranchType::Free);
  if (zeroPointer.first) {
    if (target)
      bindLocal(target, *zeroPointer.first, Expr::createPointer(0));
  }
  if (zeroPointer.second) { // address != 0
    ExactResolutionList rl;
    resolveExact(*zeroPointer.second, address, rl, "free");
    
    for (Executor::ExactResolutionList::iterator it = rl.begin(), 
           ie = rl.end(); it != ie; ++it) {
      const MemoryObject *mo = it->first.first;
      if (mo->isLocal) {
        terminateStateOnError(*it->second, "free of alloca",
                              StateTerminationType::Free,
                              getAddressInfo(*it->second, address));
      } else if (mo->isGlobal) {
        terminateStateOnError(*it->second, "free of global",
                              StateTerminationType::Free,
                              getAddressInfo(*it->second, address));
      } else {
        it->second->addressSpace.unbindObject(mo);
        if (target)
          bindLocal(target, *it->second, Expr::createPointer(0));
      }
    }
  }
}

void Executor::resolveExact(ExecutionState &state,
                            ref<Expr> p,
                            ExactResolutionList &results, 
                            const std::string &name) {
  p = optimizer.optimizeExpr(p, true);
  // XXX we may want to be capping this?
  ResolutionList rl;
  state.addressSpace.resolve(state, solver, p, rl);
  
  ExecutionState *unbound = &state;
  for (ResolutionList::iterator it = rl.begin(), ie = rl.end(); 
       it != ie; ++it) {
    ref<Expr> inBounds = EqExpr::create(p, it->first->getBaseExpr());

    StatePair branches =
        fork(*unbound, inBounds, true, BranchType::ResolvePointer);

    if (branches.first)
      results.push_back(std::make_pair(*it, branches.first));

    unbound = branches.second;
    if (!unbound) // Fork failure
      break;
  }

  if (unbound) {
    terminateStateOnError(*unbound, "memory error: invalid pointer: " + name,
                          StateTerminationType::Ptr, getAddressInfo(*unbound, p));
  }
}

ref<Expr> Executor::computeSimplifiedOffset(ExecutionState &state, ref<Expr> address, ref<Expr> base, bool &success) {
  assert(address->getWidth() == 64);
  assert(base->getWidth() == 0);

  if (AddExpr *add = dyn_cast<AddExpr>(address)) {
    ref<Expr> leftEqCond = EqExpr::create(convertToInteger(state, add->left), base);
    bool solver_success = solver->mustBeTrue(state.getConstraints(/*useHeapConstraints=*/true), leftEqCond, success,
                                        state.queryMetaData);
    assert(solver_success && "FIXME: Unhandled solver failure");
    if (success) {
      return add->right;
    }

    ref<Expr> rightEqCond = EqExpr::create(convertToInteger(state, add->right), base);
    solver_success = solver->mustBeTrue(state.getConstraints(/*useHeapConstraints=*/true), rightEqCond, success,
                                        state.queryMetaData);
    assert(solver_success && "FIXME: Unhandled solver failure");
    if (success) {
      return add->left;
    }

    // recursive case
    ref<Expr> left = computeSimplifiedOffset(state, add->left, base, success);
    if (success)
      return AddExpr::create(left, add->right);

    ref<Expr> right = computeSimplifiedOffset(state, add->right, base, success);
    if (success)
      return AddExpr::create(add->left, right);

    // another tricky part for getting offset @see examples/pointer-with-constant
    // we want to know whether this addition's left part + (right part's left part) is equal to base address
    // TODO: make this more general
    if (AddExpr *right = dyn_cast<AddExpr>(add->right)) {
      ref<Expr> eqCond = EqExpr::create(convertToInteger(state, AddExpr::create(add->left, right->left)), base);
      solver_success = solver->mustBeTrue(state.getConstraints(/*useHeapConstraints=*/true), eqCond, success,
                                          state.queryMetaData);
      if (success) {
        return right->right;
      }
    }

    return NULL;
  } else {
    ref<Expr> baseEqCond = EqExpr::create(convertToInteger(state, address), base);
    bool solver_success = solver->mustBeTrue(state.getConstraints(/*useHeapConstraints=*/true), baseEqCond, success,
                                        state.queryMetaData);
    assert(solver_success && "FIXME: Unhandled solver failure");
    if (success) {
      return ConstantExpr::create(0, 64);
    }

    return NULL;
  }
}

bool Executor::forallElemInstantiated(ExecutionState &state, ForallElemProperty *fep, ref<Expr> address) {
  for (auto inst : state.instantiatedFEPs[fep]) {
    ref<Expr> same = EqExpr::create(inst, address);

    bool res;
    solver->mustBeTrue(state.getConstraints(/*useHeapConstraints=*/true), same, res,
                                        state.queryMetaData);
    if (res)
      return true; 
  }
  return false;
}

void Executor::instantiateForallElem(ExecutionState &state,
                                    const MemoryObject *mo,
                                     ref<Expr> offset,
                                     ref<Expr> address) {
  std::vector<ForallElemProperty *> feps = mo->forallElem;
  assert(feps.size() > 0 );  

  for (auto fep : feps) {
    // skip properties that have already been instantiated for this address.
    if (forallElemInstantiated(state, fep, address)) {
      continue;
    }

    // For now, we only specify forallElem properties for 64-bit fields.
    ref<Expr> elem_offset = SubExpr::create(offset, fep->arrayOffset);
    ref<Expr> elem_aligned = EqExpr::create(URemExpr::create(elem_offset, ConstantExpr::create(fep->elemSize, 64)),
                                            ConstantExpr::create(0, 64));

    ref<Expr> inBounds = UleExpr::create(elem_offset, 
      MulExpr::create(
        ConstantExpr::create(fep->elemSize, 64),
          SubExpr::create(fep->numElems,
            ConstantExpr::create(1, 64))));

    ref<Expr> isElemRead = AndExpr::create(elem_aligned, inBounds);
    ref<Expr> check = AndExpr::create(fep->placeholderCond, isElemRead);

    bool success;
    bool solver_success = solver->mustBeTrue(state.getConstraints(/*useHeapConstraints=*/true), isElemRead, success,
                                        state.queryMetaData);
    assert(solver_success && "FIXME: Unhandled solver failure");

    if (!success)
      continue;

    // -- There is a match, instantiate the forallElem property. -- //
    tpot_message("Instantiating forallElem property");
    
    // find out which index was used..
    // we need the index in bitvector form, unfortunately..
    //! this part is a bit hacky..
    // TODO: make this more general
    ref<Expr> offset_bv;
    if (address->getWidth() == 0) {
      // this is a heap object.
      assert(mo->uniqueHeapAddress);
      offset_bv = computeSimplifiedOffset(state, address->bvForm, mo->uniqueHeapAddress, success);
    } else {
      // this is global/stack objext
      assert(mo->address);
      offset_bv = offset;
    }
    // CC: April update: not sure why I needed computeSimplifiedOffset. Perhaps because I had not implemented getBVForm?
    // assert(offset_bv && "Expected a simplified offset");
    if (offset_bv.isNull()) {
      offset_bv = BV2IntExpr::getBVForm(offset);
    }
    ref<Expr> array_offset_bv = fep->arrayOffset;
    if (array_offset_bv->getWidth() == 0) {
      array_offset_bv = BV2IntExpr::getBVForm(fep->arrayOffset);
    }
    ref<Expr> elem_offset_bv = SubExpr::create(offset_bv, array_offset_bv);

    ref<Expr> idx = UDivExpr::create(elem_offset_bv, ConstantExpr::create(fep->elemSize, 64));

    std::vector<ref<Expr>> args; 

    // push the address of the base of the element.
    // since we check earlier whether the read is elem-aligned, we can use _address_ directly.
    // TODO: perhaps this pointer is redundant.. Let's think about removing it from the API
    args.push_back(BV2IntExpr::getBVFormOptional(address));
    args.push_back(idx);

    // assume the property over initial states (thus the Memoized).
    
    // [dummy object logic]
    // // Currently, forallElem properties are written for a pointer field (e.g., next).
    // // We need to pass the object state of the pointed-to object to the lambda.
    // // This is due to an implementation limitaiton related to instantiating forallZone objects
    // // within lambdas computed over the initial state for memoization.
    
    // need to include resolution path constraints from the memoization. Let's use a fresh state.
    ExecutionState *freshState = state.branch();

    ExecutionState *unbound = &state;

    // the dummyObject should only be used if memoResPath is not feasible (or
    // provably does not result in fzone resolution). In both cases, no read
    // from the object should matter.
    const ObjectState *unboundOSPt = lambdaMemos[fep->condFunc].dummyObject;
    bool resPathFeasible;

    ref<Expr> memoResPath = lambdaMemos[fep->condFunc].fzoneResPath;
    // assert(memoResPath);
    if (!memoResPath) {
      assert (unboundOSPt == NULL);
      goto no_mem_res_path;
    }
    assert(false);
    //! [dummy object logic] Fix this.
    // for (int i = 0; i < args.size(); i++) {
    //   ref<Expr> mem_arg = lambdaMemos[fep->fptr].arguments[i];
    //   assert(mem_arg->getWidth() == args[i]->getWidth());

    //   // We need to replace the argument with the actual value.
    //   ExprReplaceVisitor visitor(mem_arg, args[i]);
    //   memoResPath = visitor.visit(memoResPath);
    // }
    // resPathFeasible = addConstraintGuarded(*freshState, memoResPath, /*failureIsFatal=*/false);
    // if (resPathFeasible) {
    //   NoOpResolutionList rl = resolveAddressNoOp(*freshState, /*used to be readResult*/, NULL, NULL, 0, "");

    //   for (auto i : rl.objects) {
    //     assert(unbound);
    //     const MemoryObject *pointedTo = i.first;
    //     ref<Expr> cond = i.second;

    //     // ! careful: do we want to fork on inbounds or offsetEq?
    //     // ! Could we be missing the bitvector constraints here?
    //     // cond = BV2IntExpr::getBVForm(cond);

    //     StatePair branches = fork(*unbound, cond, true, BranchType::MemOp);
    //     assert(branches.first && "Expected a branch");
    //     assert((branches.second || !rl.fzone.first) && "Expected a branch");
    //     ExecutionState *bound = branches.first;
    //     bound->forkReason = "[forallElem inst] resolution into object: " + pointedTo->name;

    //     auto osPt = bound->heap.findObject(pointedTo);
    //     assert(osPt);

    //     ref<Expr> constr = computeLambdaMemoized(*bound, fep->fptr, args, NULL, osPt);
    //     //! simplify here, as per the comment above.

    //     // constr = doTpotSimplifications(*bound, constr);

    //     // Also need to check if the object has been modified at this offset.
    //     // TODO: handle forall_elem properties over global arrays (which are not on the heap).
    //     // const ObjectState *os = bound->heap.findObject(mo);
    //     // assert(os && "Object not found in heap");

    //     // We do not pass reads from potentially modified object states to instantiateForallElem anymore,
    //     // so we should nor need to exclude modified indices.
    //     // bool addSuccess = addConstraintGuarded(*bound,
    //     //                     OrExpr::create(os->modifiedAt(offset, width),
    //     //                       constr),
    //     //                       /*failureIsFatal=*/false);
    //     bool addSuccess = addConstraintGuarded(*bound,
    //                           constr,
    //                           /*failureIsFatal=*/false);
    //     if (addSuccess) {
    //       bound->instantiatedFEPs[fep].push_back(address);
    //     } else {
    //       // turns out this state is infeasible (and we only noticed after instantiating the property).
    //       // kill the state without failing.
    //       tpot_message("State made infeasible by forallElem property. Fork reason: %s", bound->forkReason.c_str());
    //       terminateState(*bound);
    //     }

    //     unbound = branches.second;
    //   }

    //   if (rl.fzone.first) {
    //     ExecutionState *pseudoChild = unbound->branch();
    //     // Pretend that pseudoChild is a lambda state forked from
    //     // _state_ , so that we can conditionally allocate the object on _state_.
    //     // !This is a bit hacky. We should do this at a higher level of abstraction.
    //     std::vector<ref<Expr>> pc = {};
    //     pseudoChild->lambdaPathConstraints.push_back(std::vector<ref<Expr>>());
    //     pseudoChild->lambdaParent = unbound;
    //     pseudoChild->lambdaPurpose = INSTANTIATE;
    //     pseudoChild->lambdaFunction = NULL;
    //     addConstraintGuarded(*pseudoChild, memoResPath);
    //     // save and clear out addedStates. Otherwise allocateInHeap will consider addedStates to be lambda siblings.
    //     std::vector<ExecutionState *> tmp_addedStates = addedStates;
    //     addedStates.clear();

    //     auto prevSz = pseudoChild->heap.fZoneChildren[rl.fzone.first].size(); 
    //     createFZoneInstance(*pseudoChild, rl.fzone.first, convertToInteger(state, readResult));
    //     assert(pseudoChild->heap.fZoneChildren[rl.fzone.first].size() == prevSz + 1);

    //     const MemoryObject *pointedTo = pseudoChild->heap.fZoneChildren[rl.fzone.first].back();
    //     delete pseudoChild;
    //     //restore addedStates.
    //     addedStates = tmp_addedStates;

    //     unbound->forkReason = "[forallElem inst] resolution into fresh fZoneChild: " + pointedTo->name;

    //     unboundOSPt = unbound->heap.findObject(pointedTo);
    //     assert(unboundOSPt);
    //   } 
    // }
no_mem_res_path:
    // note: unbound includes the !memoResPath case

    //.. all arguments past the first two are "frozen" for forallElem lambas.
    assert(args.size() == 2);
    for (int i = 2; i < lambdaMemos[fep->condFunc].arguments.size(); i++) {
      args.push_back(lambdaMemos[fep->condFunc].arguments[i]);
    }    

    ref<Expr> constr = computeLambdaMemoized(*unbound, fep->condFunc, args, NULL, unboundOSPt); 
    //                                         //

    bool feasible = addConstraintGuarded(*unbound, constr, /*failureIsFatal=*/false); 
    if (!feasible) {
      // turns out this state is infeasible (and we only noticed after instantiating the property).
      // kill the state without failing.
      tpot_message("Pruning state due to forallElem instantiation");
      terminateState(*unbound);
    } else {
      unbound->instantiatedFEPs[fep].push_back(address);   
    }
    delete freshState;
  }
}

// each state has a single constraint for each fzone in it. This function
// returns the index of that constraints in the state's fzoneOnly constraint vector.
// ! --- 
// this is a bit hacky. We rely on indices being the same between the fzoneOnly vector
// and the heapObjects vector. This is true because we add the fzoneOnly constraints
// to the state's constraint vector in the same order as we add the fzone objects to
// the heapObjects vector. (due to the if(!namesObjForall) return false; pattern)
int Executor::findFZoneIdx(ExecutionState &state, const ForallZone *fzone) {
  int i = 0;
  for (; i < state.heap.fzones.size(); i++) {
    if (state.heap.fzones[i] == fzone) {
      break;
    } 
  }
  assert(i < state.constraints_fZoneOnly.size() && "Could not find fZone constraint");
  return i;
}

// symmetric to findFZoneIdx
const ForallZone *Executor::findFZone(ExecutionState &state, int targetIdx) {

  return state.heap.fzones[targetIdx];
}

void Executor::addFZoneChild(ExecutionState &state, const ForallZone *fzone, SytSSMemoryObject *smo) {
  auto it = state.heap.fZoneChildren.find(fzone);
  if (it == state.heap.fZoneChildren.end()) {
    state.heap.fZoneChildren[fzone] = std::vector<const SytSSMemoryObject *>();
  }
  state.heap.fZoneChildren[fzone].push_back(smo);
}

// given address that resolves into a forall zone, determine (address - base) where base is the address of the 
// object-to-be-spawned captured by the forall zone.
ref<Expr> Executor::determineOffset(ExecutionState &state, ref<Expr> address, int fZoneIdx) {
  assert(address->getWidth() == 0);

  // toConstant is temporarily broken.. For now, just try out a few different values..
  int64_t offsetCandidates[] = {0, 0, 8, 16};
  if (address->getKind() == Expr::Add) {
    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(address->getKid(0))) {
      int64_t c= CE->getZExtValue();

      ForallZone *fz = state.heap.fzones[fZoneIdx];
      // find the element size
      std::vector<ref<Expr>> args;
      args.push_back(BitVecExpr::create("unused", 64));
      ref<Expr> elemSize = computeLambdaMemoized(state, fz->size_fptr, args, NULL, NULL);
      if (ConstantExpr *elemSizeConst = dyn_cast<ConstantExpr>(elemSize)) {
        if (c < elemSizeConst->getZExtValue()) {
          offsetCandidates[0] = c;
        }
      } else {
        assert(0 && "We didn't account for this yet.");
      }
    }
  }

  ref<Expr> constOffset;
  bool success;
  for (int i = 0; i < sizeof(offsetCandidates) / sizeof(uint64_t); i++) {
    constOffset = ConstantExpr::create(offsetCandidates[i], 0);
    
    // Try out the offset candidate. Is (addr - cand) allocated?
    if (!checkHeapSafety(state, SubExpr::create(address, constOffset), /*bytes=*/ ConstantExpr::create(1, 64),
                              /*useFZoneConstraints=*/true, fZoneIdx)) {
      // candidate too large
      continue;
    }
    // Is (addr - cand - 1) allocated?
    //! temporarily disable this
    // if (checkHeapSafety(state, SubExpr::create(SubExpr::create(address, constOffset),
    //                                             ConstantExpr::create(1, 64)), 
    //                           /*bytes=*/ ConstantExpr::create(1, 64),
    //                           /*useFZoneConstraints=*/true, fZoneIdx)) {
    //   // candidate too small
    //   continue;
    // }

    // ref<Expr> cond = EqExpr::create(SubExpr::create(address, constOffset), fzone->uniqueHeapAddress);

    // solver->mustBeTrue(state.getConstraints(true, true, fZoneIdx), cond, success,
    //                         state.queryMetaData);
    // if (success)
    //   break;
    return constOffset;
  }
  assert(0 && "Could not determine offset");
  return NULL;
}

// Path condition + extraConstraints imply that address is in mo. Do they also guarantee a constant offset into mo?
ref<Expr> Executor::determineOffset(ExecutionState &state, ref<Expr> address, const MemoryObject *mo ,ref<Expr> extraConstraints) {
  int64_t offsetCandidates[] = {0, 0, 8, 16};
  if (address->getKind() == Expr::Add) {
    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(address->getKid(0))) {
      offsetCandidates[0] = CE->getZExtValue();
    }
  }

  ConstraintSet c = state.getConstraints(true);
  if (!extraConstraints.isNull()) {
    std::vector<ref<Expr>> singletonVector = {extraConstraints};
    ConstraintSet singleton(singletonVector);

    c = c.join(singleton);
    c.readSimplCache = state.getConstraints(true).readSimplCache;
    c.readSimplKnownFailures = state.getConstraints(true).readSimplKnownFailures;
    c.addressSimplTable = state.getConstraints(true).addressSimplTable;
  } 

  for (int i = 0; i < sizeof(offsetCandidates) / sizeof(uint64_t); i++) {
    ref<Expr> constOffset = ConstantExpr::create(offsetCandidates[i], 0);
    ref<Expr> cond = EqExpr::create(SubExpr::create(address, constOffset), mo->uniqueHeapAddress);
    if (!extraConstraints.isNull()) {
      cond = OrExpr::create(cond, NotExpr::create(extraConstraints));
    }
    

    bool success;
    solver->mustBeTrue(c, cond, success, state.queryMetaData);
    if (success)
      return constOffset;
  
  }
  return NULL;
}

bool Executor::addressSimpl_tryZero(ExecutionState &state, ref<Expr> expr) {
  ref<Expr> isZero = EqExpr::create(expr, ConstantExpr::create(0, 64));
  bool success;
  LOG_SIMPLIFIER("-- addressSimpl_tryZero --");
  solver->mustBeTrue(state.getConstraints(/*useHeapConstraints=*/true), isZero, success,
                                        state.queryMetaData);
  if (success) {
    updateAddressSimplTable(state, expr, ConstantExpr::create(0, 64));
    // Also good chances that this is a sub, making its operands equal
    if (const SubExpr *sub = dyn_cast<SubExpr>(expr)) {
      updateAddressSimplTable(state, sub->left, sub->right);
    }
    return true;
  }
  return false;
}

void Executor::learnAddressSimpl(ExecutionState &state,
      ref<Expr> address, ref<Expr> base, ref<Expr> offset) {
  if (dyn_cast<ConstantExpr>(offset)) {
    // this will typically happen for new fzone instances, 
    // since determineOffset will have been called.
    updateAddressSimplTable(state, address, 
      AddExpr::create(base, offset));
    return;
  } 

  if (AddExpr *add = dyn_cast<AddExpr>(offset)) {
    if (dyn_cast<ConstantExpr>(add->left)) {
      // Due to Klee's expression canonicalization, there's a 
      // good chance right must be zero.
      if (addressSimpl_tryZero(state, add->right))
        return;
    }
  }

  // try simplifiyng offset to zero
  if (addressSimpl_tryZero(state, offset)) {
    return;
  }

  // -- try going one level deeper -- //
  // Is offset of the form  (A + X) - B where A and B must be equal?
  if (const SubExpr *sub = dyn_cast<SubExpr>(offset)) {
    if (const AddExpr *add = dyn_cast<AddExpr>(sub->left)) {
      // tryZero is applicable if we rewrite as X + (A - B)
      if (addressSimpl_tryZero(state, SubExpr::create(add->left, sub->right)))
        return;

      // what if X must be equal to B?
      if (addressSimpl_tryZero(state, SubExpr::create(add->right, sub->right)))
        return;
    }
  }

  // Do we have the same case as above, but with a constant added? C + ((A + X) - B)
  if (const AddExpr *add = dyn_cast<AddExpr>(offset)) {
    if (dyn_cast<ConstantExpr>(add->left)) {
      learnAddressSimpl(state, address, base, add->right);
      return;
    }
  }

  //raise(SIGINT);
}

void Executor::executeInBoundsMemOp(ExecutionState &state,
                                    AddressSpace &as,
                                    memop_type mop,
                                    const MemoryObject *mo,
                                    const ObjectState *os,
                                    ref<Expr> offset,
                                    ref<Expr> address,
                                    ref<Expr> value, /* undef if not write */
                                    KInstruction *target /* undef if not read */,
                                    std::string name  /* undef if not name */,
                                    Expr::Width type
                                    ) {
  if (mo->uniqueHeapAddress) {
    learnAddressSimpl(state, address, mo->uniqueHeapAddress, offset);

    const SytSSObjectState *ssos = dynamic_cast<const SytSSObjectState *>(os);
    assert(ssos);
    if (ssos->isFreed) {
      terminateStateOnUserError(state, "memory error: object freed");
    }
  }                                    
  
  ref<Expr> result;
  AddressSpace *asPtr = NULL;  
  switch (mop) {
  case MEMOP_WRITE:
    if (state.computeOldValues && !mo->isLocal) {
      // this is very likely a mistake
      terminateStateOnError(state, "Global write during old value computation",
                            StateTerminationType::ReadOnly);
    }
    if (os->readOnly) {
      terminateStateOnError(state, "memory error: object read only",
                            StateTerminationType::ReadOnly);
    } else {
      // We trigger forallElem instantiation on writes, too.. 
      // This seems to address some case-splitting incompleteness problems with the bv2int trick.
      // TODO: add a link to a query that demonstrates the incompleteness.

      if (!mo->forallElem.empty()) {
        auto prevSz = addedStates.size(); //! tmp
        instantiateForallElem(state, mo, offset, address);
        // This might now fork the state... Deal with it.
        if (addedStates.size() > prevSz) {
          // We will need to distignguish between states forked by instantiateForallElem 
          // and those forked previously if this assertion fails.
          assert(prevSz == 0 && "Expected no forks due to instantiateForallElem");
        }
      }

      // Actually do the write.
      ObjectState *wos = as.getWriteable(mo, os);
      // write optimized bytes at optimized addresses
      offset = doTpotSimplifications(state, offset);
      value = doTpotSimplifications(state, value);
      wos->write(offset, value);

      if (!mo->isLocal) {
        state.isModified = true;
        state.modifiedGlobals.insert(mo);
      }
    }   
    break;
  
  case MEMOP_READ:
    result = os->read(offset, type, /*ignoreWrites=*/state.computeOldValues && !mo->isLocal);
    
    if (interpreterOpts.MakeConcreteSymbolic)
      result = replaceReadWithSymbolic(state, result);


    if (!mo->forallElem.empty()) {
      auto prevSz = addedStates.size(); //! tmp
      instantiateForallElem(state, mo, offset, address);
      // This might now fork the state... Deal with it.
      if (addedStates.size() > prevSz) {
        // We will need to distignguish between states forked by instantiateForallElem 
        // and those forked previously if this assertion fails.
        assert(prevSz == 0 && "Expected no forks due to instantiateForallElem");
        for (auto s : addedStates) {
          bindLocal(target, *s, result);
        } 
      }
    }
    if (state.syt_stage == EXECUTE_TEST)
      mo->accessed = true;

    if (state.invBeingAssumed != NULL) {
      // update invariant dependencies (in the lambda root)
      auto s = &state;
      while (s->lambdaParent) {
        s = s->lambdaParent;
      }
      assert(s->invBeingAssumed == state.invBeingAssumed);
      s->invDependencies[state.invBeingAssumed].insert(mo);
    }

    bindLocal(target, state, result);
    break;

  case MEMOP_NAME:
    /* this is a dirty solution that allows invariants to claim objects before the leak check*/
    // Need to determine if the object is in the original heap or a havoced heap
    asPtr = NULL;
    for (auto inv: state.activeInvariants) {
      if (inv.heap == &as) {
        asPtr = inv.heap;
        break;
      }
    }
    if (!asPtr) {
      assert(&as == &state.heap);
      asPtr = &as;
    } else {
      //..... moreoever, naming the object in the havoced heap does not make sense..
      // we need to name the original object, as the leak check is done there....

      // TODO: this depends on object-granularity naming instead of byte-granularity naming.
      // TODO: fix this.

      // TODO: there needs to be an easier way to recover the object than another full memory resolution.
      // for now, here goes...
      ExecutionState *oobState;
      NoOpResolutionList res = resolveInHeapNoOp(state, address, NULL, NULL,
                               0, "", state.heap, Expr::getMinBytesForWidth(type), type, oobState);
      assert(res.isSingleResolution());
      const MemoryObject *originalMo = res.objects[0].first;
      const ObjectState *originalOs = state.heap.findObject(originalMo);

      asPtr = &state.heap;
      mo = originalMo;
      os = originalOs;
    }
    // -----

    if (state.nameParentsObjects) {
      assert(state.lambdaParent);
      asPtr = &state.lambdaParent->heap;
    }


    if (asPtr->getWriteable(mo, os)->name(name)) {
      // terminateStateOnUserError(*bound, "cannot name object",
      //                           StateTerminationType::User);
      state.heap.namesToObjects[name] = std::make_pair(address, ref<Expr>(nullptr));

      if (state.invBeingAssumed != NULL) {
        // update invariant namings (in the lambda root)
        auto s = &state;
        while (s->lambdaParent) {
          s = s->lambdaParent;
        }
        assert(s->invBeingAssumed == state.invBeingAssumed);
        s->invNamings[state.invBeingAssumed].push_back(std::make_pair(mo, name));
      }

      bindLocal(target, state, ConstantExpr::create(1, Expr::Bool));
    } else {
      bindLocal(target, state, ConstantExpr::create(0, Expr::Bool));
    }
    break;

  case MEMOP_NOP:
    break;
  default:
    assert(0 && "invalid memory operation");
    break;
  }
}


// enum MemOpResult {MemOp_Success, MemOp_OOB, MemOp_Error};

// returns true if the memop only resolves to known objects in as.
// that is, returns false if there is an oob resolution.
MemOpResult Executor::trySingleResolution(ExecutionState &state,
                                        memop_type mop,
                                        ref<Expr> address,
                                        ref<Expr> value /* undef if not write */,
                                        KInstruction *target /* undef if not read */,
                                        Expr::Width objSize  /* undef if not name */,
                                        std::string name  /* undef if not name */,
                                        AddressSpace &as, 
                                        unsigned bytes,
                                        Expr::Width type,
                                        bool useHeapConstraints,
                                        bool useFZoneConstraints,
                                        int fZoneIdx) {
  // This assertion is weird, but let's keep it. 
  // Something has gone horribly wrong if it fails.
  bool isBaseMem = (&as == &state.addressSpace || &as == &state.heap);
  if (!isBaseMem) {
    bool success = false;
    for (auto inv: state.activeInvariants) {
      if (inv.addressSpace == &as || inv.heap == &as) {
        success = true;
        break;
      }
    }
    assert(success && "Invalid address space");
  }

  if (SimplifySymIndices) {
    if (!isa<ConstantExpr>(address))
      address = ConstraintManager::simplifyExpr(state.constraints, address);
    if (mop == MEMOP_WRITE && !isa<ConstantExpr>(value))
      value = ConstraintManager::simplifyExpr(state.constraints, value);
  }

  address = optimizer.optimizeExpr(address, true);

  // fast path: single in-bounds resolution
  ObjectPair op;
  bool success = false;

  solver->setTimeout(coreSolverTimeout);
  LOG_MEMORY_RESOLUTION("Calling resolve one");
  // Instead of changing the resolve* API's to add useFZoneConstraints,
  // we just temporarily modify the state's constraints. 
  // This is safe because we are sure that resolve* will not fork the state.
  auto tmp = state.constraints;
  state.constraints = state.getConstraints(useHeapConstraints, useFZoneConstraints, fZoneIdx);
  if (!as.resolveOne(state, solver, address, op, success)) {
    // address = toConstant(state, address, "resolveOne failure");
    // success = as.resolveOne(cast<ConstantExpr>(address), op);
  }
  solver->setTimeout(time::Span());
  state.constraints = tmp;

  if (success) {
    const MemoryObject *mo = op.first;

    if (MaxSymArraySize && mo->size >= MaxSymArraySize) {
      address = toConstant(state, address, "max-sym-array-size");
    }

    ref<Expr> relative_address = address;
    if(mo->uniqueHeapAddress) 
      relative_address = SubExpr::create(address, mo->uniqueHeapAddress);

    ref<Expr> offset = mo->getOffsetExpr(relative_address);

    ref<Expr> check = mo->getBoundsCheckOffset(offset, bytes);
    check = optimizer.optimizeExpr(check, true);

    bool inBounds;
    solver->setTimeout(coreSolverTimeout);
    ConstraintSet c = state.getConstraints(useHeapConstraints, useFZoneConstraints, fZoneIdx);
    LOG_MEMORY_RESOLUTION("Doing bounds check");
    bool success = solver->mustBeTrue(c, check, inBounds,
                                      state.queryMetaData);
    solver->setTimeout(time::Span());
    if (!success) {
      state.pc = state.prevPC;
      terminateStateOnSolverError(state, "Query timed out (bounds check).");
      return MemOp_Error;
    }

    if (inBounds) {
      const ForallZone *fzone = dynamic_cast<const ForallZone *>(mo);
      if (useFZoneConstraints && !fzone) {
        raise(SIGINT); // this is very likely a bug
      }
      if (fzone) {
        raise(SIGINT); // this is very likely a bug
      }

      executeInBoundsMemOp(state, as, mop, mo, op.second, offset, address, value,
                           target, name, type);
      return MemOp_Success;
    }
  }
  return MemOp_OOB;
}

MemOpResult Executor::tryMultipleResolution(ExecutionState &state,
                                            memop_type mop,
                                            ref<Expr> address,
                                            ref<Expr> value /* undef if not write */,
                                            KInstruction *target /* undef if not read */,
                                            Expr::Width objSize  /* undef if not name */,
                                            std::string name  /* undef if not name */,
                                            AddressSpace &as,
                                            unsigned bytes,
                                            Expr::Width type,
                                            ExecutionState *&oobState,
                                            bool useHeapConstraints,
                                            bool useFZoneConstraints,
                                            int fZoneIdx,
                                            ref<Expr> extraConstraints) {
  // This assertion is weird, but let's keep it. 
  // Something has gone horribly wrong if it fails.
  bool isBaseMem = (&as == &state.addressSpace || &as == &state.heap);
  if (!isBaseMem) {
    bool success = false;
    for (auto inv: state.activeInvariants) {
      if (inv.addressSpace == &as || inv.heap == &as) {
        success = true;
        break;
      }
    }
    assert(success && "Invalid address space");
  }

  address = optimizer.optimizeExpr(address, true);
  ResolutionList rl;  
  solver->setTimeout(coreSolverTimeout);

  auto tmp = state.constraints;
  state.constraints = state.getConstraints(useHeapConstraints, useFZoneConstraints, fZoneIdx);
  // state.constraints = state.getConstraints(useHeapConstraints);
  bool incomplete = as.resolve(state, solver, address, rl,
                                               0, coreSolverTimeout,
                                               extraConstraints);
  solver->setTimeout(time::Span());
  state.constraints = tmp;

  // XXX there is some query wasteage here. who cares?
  ExecutionState *unbound = &state;
  
  for (ResolutionList::iterator i = rl.begin(), ie = rl.end(); i != ie; ++i) {
    const MemoryObject *mo = i->first;
    const ObjectState *os = i->second;

    ref<Expr> relative_address = address;
    if(mo->uniqueHeapAddress) 
      relative_address = SubExpr::create(address, mo->uniqueHeapAddress);

    ref<Expr> inBounds = mo->getBoundsCheckPointer(relative_address, bytes);
    
    // Not sure if we need extra constraints (not in fzone) here. 
    // We don't want them added to the state, and I'm not sure we need them for the query..
    // Do we ever expect the fork to be one way?
    // ref<Expr> cond = extraConstraints.isNull() ? inBounds : AndExpr::create(inBounds, extraConstraints);
    //! important: we lose some information here in order to avoid adding extraConstraints to the state, since extraConstraints will contain a forall expression.
    //! Consider the resolution of p where (p == base_A || p in fzone). extraConstraints will be (p not in fzone).
    //! We would like to fork a state where p == base_A  (i.e. p inbounds A && p not in fzone), but since this is expensive, we drop the p not in fzone part.

    // This loses too much information to prove simple things like the "head->next->next == head" case of examples/freelist.
    // Here, we try to recover some information by looking for constrant offsets.
    // This is conceptually similar to concretizing the offset for fzone resolution (see handleFZoneResolution).
    ref<Expr> cond;
    ref<Expr> offset = determineOffset(*unbound, address, mo, extraConstraints);    
    if (!offset) {
      tpot_message("Could not determine offset. Losing information.");
      // raise(SIGINT);
      cond = inBounds;
    } else {
      cond = EqExpr::create(SubExpr::create(address, offset), mo->uniqueHeapAddress);

      // We need the constraint in bvform, too...
      ref<Expr> addressBV = BV2IntExpr::getBVForm(address);
      ref<Expr> offsetBV = BV2IntExpr::getBVForm(offset);
      ref<Expr> baseBV = BV2IntExpr::getBVForm(mo->uniqueHeapAddress);
      if (addressBV.isNull() || offsetBV.isNull() || baseBV.isNull()) {
        tpot_message("Could not convert addresses to BV forms. Losing information.");
      } else {
        // The below does not work: the false side will get not(bvexpr) or not(intexpr).. 
        // cond = AndExpr::create(cond, EqExpr::create(SubExpr::create(addressBV, offsetBV), baseBV));
        // Instead, just use the constraint over bvforms. The integer constraints will be added to each 
        // state (in addConstraint) while forking.
        cond = EqExpr::create(SubExpr::create(addressBV, offsetBV), baseBV);
      }
    }
    

    StatePair branches = fork(*unbound, cond, true, BranchType::MemOp);
    ExecutionState *bound = branches.first;

    // bound can be 0 on failure or overlapped 
    if (bound) {
      bound->forkReason = "Resolution into object: " + mo->name;
      AddressSpace *targetAS = NULL;
      if (isBaseMem) {
        if (&as == &state.heap)
          targetAS = &bound->heap;
        else
          targetAS = &bound->addressSpace;
      } else {
        bool success = false;
        for (int i = 0; i < state.activeInvariants.size(); i++) {
          if (state.activeInvariants[i].heap == &as) {
            targetAS = bound->activeInvariants[i].heap;
            break;
          }
          if (state.activeInvariants[i].addressSpace == &as) {
            targetAS = bound->activeInvariants[i].addressSpace;
            break;
          }
        }
        assert(targetAS && "Invalid address space");
      }
      bound->multipleResHistory.push_back(std::make_pair(target, mo->name));
      executeInBoundsMemOp(*bound, *targetAS, mop, mo, os, mo->getOffsetExpr(relative_address), 
                          address, value, target, name, type);
    }

    unbound = branches.second;
    if (!unbound)
      break;
    unbound->forkReason = "foo";
  }
  
  // XXX should we distinguish out of bounds and overlapped cases?
  if (unbound) {
    if (incomplete) {
      terminateStateOnSolverError(*unbound, "Query timed out (resolve).");
    } else {
      oobState = unbound;
      return MemOp_OOB;
    }
  }
  return MemOp_Success;
}

ref<Expr> Executor::simplifyPointer(ExecutionState &state, ref<Expr> ptr) {
  ref<Expr> res = NULL;
  switch (ptr->getKind()) { 
    case Expr::Select: {
      // See if the condition is provably true or false.

      SelectExpr *se = cast<SelectExpr>(ptr);
      ref<Expr> cond = se->cond;

      bool success;
      LOG_SIMPLIFIER("-- trying to simplify ITE pointer : true branch --");
      bool solver_success = solver->mustBeTrue(state.constraints, cond, success,
                                          state.queryMetaData);
      if (success) {
        res = se->trueExpr;
      } else {
        LOG_SIMPLIFIER("-- trying to simplify ITE pointer : false branch --");
        solver_success = solver->mustBeTrue(state.constraints,
                                          NotExpr::create(cond), success,
                                          state.queryMetaData);
        if (success)
          res = se->falseExpr;
      }
    }
  }

  if (res.isNull()) {
    return ptr;
  }

  updateAddressSimplTable(state, ptr, res);
  return res;
}

bool Executor::checkHeapSafety(ExecutionState &state, ref<Expr> _address, ref<Expr> bytes, 
                              bool useFZoneConstraints, int &fZoneIdx) {
  // assert(bytes->getWidth() == Expr::Int64 && "Expected 64-bit integer");

  // checking heap safety of complicated pointers is expensive.
  // try to simplify pointer first.
  ref<Expr> address = simplifyPointer(state, _address);

  // Constant expressions can't be heap safe.. right?
  if (dyn_cast<ConstantExpr>(address))
    return false;

  if (address->getWidth() != 0) {
    address = convertToInteger(state, address);
  }

  ref<Expr> base = IntExpr::create("is_uniq_base");

  std::vector<ref<Expr>> args;
  args.push_back(base);
  ref<Expr> base_uniq_sz = FuncAppExpr::create("is_unique", args);

  ref<Expr> check = ExistsExpr::create(base, fitsInBounds(address, bytes, base, base_uniq_sz));

  // fast path: bind variable to address itself.
  std::vector<ref<Expr>> args2 = {address};
  ref<Expr> addr_uniq_sz = FuncAppExpr::create("is_unique", args2);
  ref<Expr> check_fastPath = fitsInBounds(address, bytes, address, addr_uniq_sz);

  bool success;
  check = optimizer.optimizeExpr(check, true);
  solver->setTimeout(coreSolverTimeout);

  ref<Expr> sanity_check = ConstantExpr::create(0, Expr::Bool);

  fZoneIdx = state.constraints_fZoneOnly.size() - 1;
  if (useFZoneConstraints && fZoneIdx < 0) {
    terminateStateOnError(state, "Memory safety error: no fzones, but trying to use fzone constraints",
                          StateTerminationType::USERERR);
  }
  // if useFZoneConstraints is true, instead of addding all constraints, try them one by one.
  // In our memory model, there should always be one relevant fZone constraint.
  do {
    ConstraintSet c = state.getConstraints(/*useHeapConstraints=*/true, useFZoneConstraints, fZoneIdx);

    bool solver_success;
    // only for debugging purposes
      // can't discharge sanity check using mustBeTrue, as the fast path will 
      // keep the query from making it to the solver. 
      solver_success = solver->solver->impl->computeTruth(Query(c, sanity_check), success);
      // solver_success = solver->mustBeTrue(c, sanity_check, success,
      //                                 state.queryMetaData);
      assert(solver_success && "FIXME: Unhandled solver failure");
      assert(!success && "Sanity check failed, constraints are infeasible");
    // ----

    // try the fast path
    LOG_SIMPLIFIER("-- trying fast path for checkHeapSafety--");
    solver_success = solver->mustBeTrue(c, check_fastPath, success,
                                      state.queryMetaData);
    solver->setTimeout(time::Span());
    if (success) {
      return true;
    }

    LOG_SIMPLIFIER("-- trying slow path for checkHeapSafety--");
    solver_success = solver->mustBeTrue(c, check, success,
                                      state.queryMetaData);
    solver->setTimeout(time::Span());
    if (!solver_success) {
      state.pc = state.prevPC;
      terminateStateOnSolverError(state, "Query timed out (is_uniqptr check).");
      // TODO: this return is weird
      return false;
    }
  } while (useFZoneConstraints && !success && --fZoneIdx >= 0);

  return success;
}

bool Executor::checkHeapSafety(ExecutionState &state, ref<Expr> address, unsigned bytes, bool useFZoneConstraints, int &fZoneIdx) {
  ref<Expr> bytes_expr = ConstantExpr::alloc(bytes, Context::get().getPointerWidth());
  return checkHeapSafety(state, address, bytes_expr, useFZoneConstraints, fZoneIdx);
}

MemoryObject *Executor::createFreshHeapObject(ExecutionState &state, ref<Expr> address, unsigned bytes) {
  raise(SIGINT);
  static int index = 1; // to give fresh symbols unique names

  // We need to find the base and the size of the unique heap. 
  // This implementation is not complete... E.g. when uniqueness assumptions
  // are made in quantified formulas, we can't find exact base and size even though
  // we can safely execute the memory operation.

  // by default, the object is based at address and has size bytes.
  ref<Expr> uniqobj_base = address;
  ref<Expr> uniqobj_size = NULL;

  // We first check a few candidates from the "hints".
  for (auto h : uniqPtrHints) {
    ref<Expr> cand_base = h.first;
    ref<Expr> cand_size = h.second;

    // check if both of the folllwoing must hold:
    // * cand_base is unique for cand_size bytes.
    // * the memory access fits in [cand_base, cand_base + cand_size)

    std::vector<ref<Expr>> args;
    args.push_back(cand_base);
    ref<Expr> cand_uniq_sz = FuncAppExpr::create("is_unique", args);

    ref<Expr> cand_true = EqExpr::create(cand_uniq_sz, cand_size);

    ref<Expr> fits = AndExpr::create(
      AndExpr::create(
        UleExpr::create(ConstantExpr::alloc(bytes, Context::get().getPointerWidth()), cand_size),
        UleExpr::create(cand_base, address)),
      UleExpr::create(
        SubExpr::create(address, cand_base),
        SubExpr::create(cand_size, ConstantExpr::alloc(bytes, Context::get().getPointerWidth()))
      )
    );

    ref<Expr> cand_check = AndExpr::create(cand_true, fits);

    bool success;
    cand_check = optimizer.optimizeExpr(cand_check, true);
    solver->setTimeout(coreSolverTimeout);
    bool solver_success = solver->mustBeTrue(state.constraints, cand_check, success,
                                      state.queryMetaData);
    solver->setTimeout(time::Span());
    if (!solver_success) {
      state.pc = state.prevPC;
      terminateStateOnSolverError(state, "Query timed out (is_uniqptr check).");
      return NULL;
    }

    if (success) {
      // We found a candidate. Let's use it.
      uniqobj_base = cand_base;
      uniqobj_size = cand_size;
      break;
    }

  }

  MemoryObject *mo = NULL;

  if (uniqobj_size.isNull()) {
    // If we didn't find a candidate, we create a unique object that is the size of the memory access.

    mo = new MemoryObject(/*address=*/0, bytes, /*isLocal=*/false,
                                    /*isGlobal=*/true, false, /*allocSite=*/NULL,
                                    NULL, /*uniqueHeapAddress=*/uniqobj_base);
  } else if (ConstantExpr *CE = dyn_cast<ConstantExpr>(uniqobj_size)) {
    // If the size is constant, we can create a Klee MemoryObject
    mo = new MemoryObject(/*address=*/0, CE->getZExtValue(), /*isLocal=*/false,
                                    /*isGlobal=*/true, false, /*allocSite=*/NULL,
                                    NULL, /*uniqueHeapAddress=*/uniqobj_base);
  } else {
    // The size is symbolic. Create a symbolic-sized memory object
    mo = new SytSSMemoryObject(/*address=*/0, uniqobj_size, /*isLocal=*/false,
                                    /*isGlobal=*/true, false, /*allocSite=*/NULL,
                                    NULL, /*uniqueHeapAddress=*/uniqobj_base);
  }

  // no need to call bindObjectInState since we are calling executeMakeSymbolic anyway.
  //bindObjectInState(state, mo, /*isLocal=*/false);
  auto name = "syt_uniq_obj__" + std::to_string(index++);
  mo->setName(name);

  executeMakeSymbolic(state, mo, name);
  return mo;
}

MemOpResult Executor::resolveInHavocedMem(ExecutionState &state,
                                            memop_type mop,
                                            ref<Expr> address,
                                            ref<Expr> value /* undef if not write */,
                                            KInstruction *target /* undef if not read */,
                                            Expr::Width objSize  /* undef if not name */,
                                            std::string name  /* undef if not name */,
                                            AddressSpace &as,
                                            unsigned bytes,
                                            Expr::Width type,
                                            ExecutionState *&oobState) {
  ExecutionState *curState = &state;
  MemOpResult res;
  for (int i = state.activeInvariants.size() -1;
      i >= 0; i--) {
    Heap *havoced_heap = curState->activeInvariants[i].heap;
    AddressSpace *havoced_as = curState->activeInvariants[i].addressSpace;

    // For now, we do not support multiple resolution in addressSpace.
    res = trySingleResolution(*curState, mop, address, value, target, 
                            objSize, name, *havoced_as, bytes, type);
    if (res == MemOp_Success || res == MemOp_Error)
      return res;

    ExecutionState *oobState = NULL;

    // Since we've disabled the heap safety check, we need to make sure here
    // that concrete addresses don't make it to resolveInHeap.  
    // Otherwise we'll generate forks that don't make sense.
    if (isa<ConstantExpr>(address)) {
      return MemOp_OOB;
    }

    res = resolveInHeap(*curState, mop, address, value, target, 
                            objSize, name, *havoced_heap, bytes, type, oobState, 
                            /*useFZoneConstraints=*/false,
                            /*tryMultiple=*/true);
    // resolveInHeap did not fork. Keep considering the current state.
    // assert(!oobState);
    // oobState = curState;

    if (res == MemOp_Success || res == MemOp_Error)
      return res;
    else {
      // this should be set since we called resolveInHeap with tryMultiple=true.
      assert(oobState);

      if (mop == MEMOP_WRITE){
        // The oobState modifies state that was not havoced by this invariant
        // It should never loop back to the invariant.s
        oobState->activeInvariants[i].nonHavocedModified = true;
      }
      curState = oobState;
    }
  }
  oobState = curState;
  return MemOp_OOB;
}

 ref<Expr> Executor::getDistinctnessConstraint(ExecutionState &state, const ForallZone *fzone) {
    static int constr_idx = 1;
    ref<Expr> i = BitVecExpr::create("i_dist_" + std::to_string(constr_idx) , 64);
    ref<Expr> j = BitVecExpr::create("j_dist_" + std::to_string(constr_idx++) , 64);

    std::vector<ref<Expr>> args;
    args.push_back(i);
    ref<Expr> ptr_i = computeLambdaMemoized(state, fzone->addr_fptr, args, NULL, NULL);
    args.clear();
    args.push_back(j);
    ref<Expr> ptr_j = computeLambdaMemoized(state, fzone->addr_fptr, args, NULL, NULL);

    // Not sure if these conversion are necessary. The final convertToInteger should be enough.
    // Let's be safe..
    ref<Expr> i_int = convertToInteger(state, i);
    ref<Expr> j_int = convertToInteger(state, j);
    ref<Expr> ptr_i_int = convertToInteger(state, ptr_i);
    ref<Expr> ptr_j_int = convertToInteger(state, ptr_j);

    // if ptr(i) and ptr(j) are equal and not null, then i == j.
    ref<Expr> distinct = ForallExpr::create(i,
      ForallExpr::create(j,
        OrExpr::create (
          NotExpr::create(
            AndExpr::create(
              EqExpr::create(ptr_i_int, ptr_j_int),
              NotExpr::create(EqExpr::create(ptr_i_int, ConstantExpr::alloc(0, 64)))
            )
          ),
          EqExpr::create(i_int, j_int)
        )
      )
    );

    std::vector<ref<Expr>> unsignedExprs; // we ignore these here.
    ref<Expr> distinct_int = BV2IntExpr::convertConstraint(distinct, unsignedExprs);
    return distinct_int;
  }

void Executor::handleFZoneResolution(ExecutionState &state, const ForallZone *fzone, ref<Expr> address, unsigned bytes,
                                     memop_type mop,
                                     ref<Expr> value /* undef if not write */,
                                     KInstruction *target /* undef if not read */,
                                     std::string name  /* undef if not name */,
                                     Expr::Width type) {
  // We know that address resolves to the fzone and children when forall constraints are used.

  int fZoneIdx = findFZoneIdx(state, fzone);
  // TODO: we compute the offset twice. Remove this.
  ref<Expr> offset = determineOffset(state, address, fZoneIdx);

  // We need to figure out which children this can point to.
  // the structure of this resembles tryMultipleResolution.
  ExecutionState *unbound = &state;
  if (state.heap.fZoneChildren.find(fzone) != state.heap.fZoneChildren.end()) {
    std::vector<const SytSSMemoryObject *> children = state.heap.fZoneChildren[fzone];
    for (auto c : children) {
      // The fzone constraints will not keep address from resolving to the child.
      // So we can check for "may resolve" without fzone constraints.
      if (Heap::mayResolveTo(*unbound, solver, c, address)) {
        // See if the distinctness of fzone pointers keeps address from resolving to c.
        // Add fzone distinctness constraint. Try again.
        // TODO: Add short path
        ref<Expr> distinctness = getDistinctnessConstraint(*unbound, fzone);
        tpot_message("Checking fzone child aliasing with distinctness constraint");
        ref<Expr> sameChild = EqExpr::create(SubExpr::create(address, offset), c->uniqueHeapAddress);
        bool distinctRes;
        bool solver_success = solver->mayBeTrue(unbound->getConstraints(true), 
                                                AndExpr::create(sameChild, distinctness), distinctRes,
                                                state.queryMetaData);
        if (!distinctRes) {
          continue;
        }

        // We found a child that address may resolve to.
        const MemoryObject *mo = c;

        ref<Expr> relative_address = address;
        if(mo->uniqueHeapAddress) 
          relative_address = SubExpr::create(address, mo->uniqueHeapAddress);

        // ref<Expr> inBounds = mo->getBoundsCheckPointer(relative_address, bytes);
        ref<Expr> inBounds = EqExpr::create(BV2IntExpr::getBVForm(relative_address), BV2IntExpr::getBVForm(offset));
        
        StatePair branches = fork(*unbound, inBounds, true, BranchType::MemOp, /*useHeapConstraints=*/true);
        ExecutionState *bound = branches.first;

        if (bound) {
          tpot_message("In state %d, resolved into fzone child: %s", bound->getID(), mo->name.c_str());
          bound->forkReason = "Resolution into fzone child: " + mo->name;
          const ObjectState *os = bound->heap.findObject(mo);
          bound->multipleResHistory.push_back(std::make_pair(target, mo->name));
          executeInBoundsMemOp(*bound, bound->heap, mop, mo, os, mo->getOffsetExpr(relative_address), 
                              address, value, target, name, type);
        }

        unbound = branches.second;
        if (!unbound) {
          // !! We need to add inBounds to the path condition. proving inBounds might rely on fzone constraints.
          addConstraintGuarded(*bound, inBounds, true, "Multiple resolution into FZone children");
          updateAddressSimplTable(*bound, relative_address, offset);
          break;
        }
      }
    }
  }

  if (unbound) {
    tpot_message("In state %d, resolved into fresh fzone child.", unbound->getID());
    executeMemOpInFreshInstance(*unbound, fzone,  mop, address, value, target, name, type);
  }
}

void Executor::updateAddressSimplTable(ExecutionState &state,
      ref<Expr> address, ref<Expr> simpl) {
  // Put (address -> base + offset) in the state's address simplification table

  // TODO: properly modularize this lookup and insertion.
  bool found = false;
  for (auto &p : state.constraints.addressSimplTable) {
    if (p.first == address) {
      found = true;
      break;
    }
  }
  if (!found) {
    state.constraints.addressSimplTable.push_back(
      std::make_pair(address, simpl));
      LOG_SIMPLIFIER("addressSimpleTable size: %d", state.constraints.addressSimplTable.size());
  }
}

void Executor::executeMemOpInFreshInstance(ExecutionState &state, const ForallZone *fzone, 
                                      memop_type mop,
                                      ref<Expr> address, 
                                      ref<Expr> value, /* undef if not write */
                                      KInstruction *target /* undef if not read */,
                                      std::string name  /* undef if not name */,
                                      Expr::Width type) {
  static unsigned fzone_inst_ctr = 1;

  int fZoneIdx = findFZoneIdx(state, fzone);
  // TODO: we compute the offset twice. Remove this.
  ref<Expr> offset = determineOffset(state, address, fZoneIdx);
  assert(offset && "Could not determine offset");

  ref<Expr> size_int;
  // First, check if the size is constant
  ref<Expr> unused_i_size = BitVecExpr::create("unused", 64);
  std::vector<ref<Expr>> args;
  args.push_back(unused_i_size);
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(computeLambdaMemoized(state, fzone->size_fptr, args, NULL, NULL))) {
    ref<ConstantExpr> const_int = ConstantExpr::alloc(CE->value);
    const_int->producesInt = true;
    size_int = const_int;
  } else {
    // could not get this to work without causing solver explosion.. We won't allow this case for now.
    assert(0);

    // // decide the size of the object to be allocated.
    // // choose a symbolic size. Add path constraint.
    // // forall_i (bound_addr(i) == base_ptr) ==> (bound_size(i) == size)
    // // ref<Expr> size = BitVecExpr::create(fzone->name + "_inst_" + std::to_string(fzone_inst_ctr) + "size", 64);
    // size = IntExpr::create(fzone->name + "_inst_" + std::to_string(fzone_inst_ctr) + "_size");
    // ref<Expr> bound_i = BitVecExpr::create("i_size_"+ std::to_string(fzone_inst_ctr), 64);
    // std::vector<ref<Expr>> args;
    // args.push_back(bound_i);
    // ref<Expr> bound_addr = computeLambda(state, fzone->addr_fptr, args);
    // ref<Expr> bound_size = computeLambda(state, fzone->size_fptr, args);
    // ref<Expr> size_constr = ForallExpr::create( bound_i,
    //   OrExpr::create(
    //     NotExpr::create(EqExpr::create(bound_addr, address->bvForm)),
    //     EqExpr::create(convertToInteger(bound_size), size)
    //   )
    // );

    // // Ideally we shouldn't need this. The above is not exactly correct.
    // size_constr = AndExpr::create(SltExpr::create(ConstantExpr::create(0, 64), size),
    //                               size_constr);
    // // This is very bad... but required to prevent the solver from exploding.
    // size_constr = AndExpr::create(size_constr,
    //                               SltExpr::create(size, ConstantExpr::create(((unsigned long int) 1 << 32) , 64)));

    // // ref<Expr> size_int = convertToInteger(size);
    // ref<Expr> size_int = size;

    // ref<Expr> size_constr_int = BV2IntExpr::convertConstraint(size_constr);

    // // When we allow fzone resolution in lambdas,
    // // this will need to be added to all states where the new object is allocated
    // addConstraint(state, size_constr_int);
  }

  ref<Expr> base_ptr_int = SubExpr::create(address, offset);
  // tmp patch for now. Not sure we'd like to keep the bvForm mechanism.
  if (!base_ptr_int->bvForm) {
    assert(offset->getKind() == Expr::Constant);
    ConstantExpr* offset_const = dyn_cast<ConstantExpr>(offset);
    base_ptr_int->bvForm = SubExpr::create(address->bvForm, ConstantExpr::alloc(offset_const->getZExtValue(), 64));
  }

  SytSSMemoryObject *smo;

  if (state.lambdaParent && state.lambdaPurpose == MEMOIZE) {
    assert(state.syt_stage == ASSUME_INVARIANTS); // we currently only memoize over the initial state.

    auto memoIt = lambdaMemos.find(state.lambdaFunction);
    assert(memoIt != lambdaMemos.end()); 
    struct LambdaMemo &memo = memoIt->second;

    // The first time an fzone resolution happens within the lambda, we need to allocate the dummy object.
    // make sure the address is as expected.

    smo = dynamic_cast<SytSSMemoryObject *>(memo.candidateObject);
    ref<Expr> expected = smo->uniqueHeapAddress;

    bool success;
    bool solver_success = solver->mustBeTrue(state.getConstraints(/*useHeapConstraints=*/true), 
      EqExpr::create(base_ptr_int, expected), success, state.queryMetaData);
    assert(solver_success && "Solver failure");
    assert(success && "fzone resolution address does not match the expected address");

    ref<Expr> lambdaPathCondition = ConstantExpr::alloc(1, Expr::Bool);
    for (auto &constraint : state.lambdaPathConstraints.back()) {
      lambdaPathCondition = AndExpr::create(lambdaPathCondition, constraint);
    }
    memo.fzoneResPath = lambdaPathCondition;

    // instead of allocating an fzone child, allocate an object on the heap
    // with the same name and size as the candidate object. We don't allocate the candidate
    // object directly, since we want the base address to be a fresh variable.
    // Over the current state, we (in allocateInHeap) add the constraint that the base address is 
    // the same as the candidate object's base address.
    smo = specialFunctionHandler->allocateInHeap(state, NULL, base_ptr_int, smo->symbolicSize, smo->name,
                                                 /*constrainSize=*/false, /*skipParents=*/true);

    memo.dummyObject = state.heap.findObject(smo);

  } else {
    auto name = fzone->name + "_inst_" + std::to_string(fzone_inst_ctr++);

    smo = NULL; // this will cause allocateInHeap to create a fresh object.
    smo = specialFunctionHandler->allocateInHeap(state, smo, base_ptr_int, size_int, name);
    state.multipleResHistory.push_back(std::make_pair(target, smo->name));
    tpot_message("Adding FZone child: %s", name.c_str());

    // this part is symmetrical to allocateInHeap. Refactor.
    addFZoneChild(state, fzone, smo);
    if (state.lambdaParent) {
      // add child to siblings
      for (auto s: addedStates) {
        // the current state is already handled
        if(s == &state) continue;
        // ignore states that are forked during the current instruction. 
        if(s->prevPC == state.prevPC) continue;

        addFZoneChild(*s, fzone, smo);
      }

      // add child to parents
      // TODO: consider parents' siblings...
      ExecutionState *cur = state.lambdaParent;
      while (cur != NULL) {
        addFZoneChild(*cur, fzone, smo);
        cur = cur->lambdaParent;
      }
    }
  }

  const MemoryObject *mo = smo;
  const ObjectState *os = state.heap.findObject(smo);

  if (ForallZoneProperty *fzp = fzone->fzoneProperty) {
    tpot_message("Instantiating forall zone property");
    std::vector<ref<Expr>> args; 
    args.push_back(BV2IntExpr::getBVForm(mo->uniqueHeapAddress));
    ref<Expr> constr = computeLambdaMemoized(state, fzp->fptr, args, NULL, os);

    //? Do we need to add this across states?
    
    // this part is symmetrical to allocateInHeap. Refactor.
    addConstraintGuarded(state, constr, true, "FZone prop: " + fzp->fptr->getName().str());
    if (state.lambdaParent) {
      // add child to siblings
      for (auto s: addedStates) {
        // the current state is already handled
        if(s == &state) continue;
        // ignore states that are forked during the current instruction. 
        if(s->prevPC == state.prevPC) continue;

        addConstraintGuarded(*s, constr, true, "FZone prop (sibling): " + fzp->fptr->getName().str());
      }

      // add child to parents
      // TODO: consider parents' siblings...
      ExecutionState *cur = state.lambdaParent;
      while (cur != NULL) {
        addConstraintGuarded(*cur, constr, true, "FZone prop (child): " + fzp->fptr->getName().str());
        cur = cur->lambdaParent;
      }
    }

  }
  offset = ConstraintManager::simplifyExpr(state.constraints, offset);
  offset = optimizer.optimizeExpr(offset, true);
  
  executeInBoundsMemOp(state, state.heap, mop, mo, os, offset, 
                            address, value, target, name, type);
}

void Executor::createFZoneInstance(ExecutionState &state, const ForallZone *fzone, ref<Expr> address) {
  executeMemOpInFreshInstance(state, fzone,  MEMOP_NOP, address, 0, 0, "", 0);
}

bool Executor::checkForLeaks(ExecutionState &state) {
  if(state.heap.checkForLeaks()) {
    interpreterHandler->incLeakyPaths();
    tpot_message("!!!!!! ------ This path leaks memory ------ !!!!!!");
    return true;
  }
  return false;
}


MemOpResult Executor::resolveInHeap(ExecutionState &state,
                                            memop_type mop,
                                            ref<Expr> address,
                                            ref<Expr> value /* undef if not write */,
                                            KInstruction *target /* undef if not read */,
                                            Expr::Width objSize  /* undef if not name */,
                                            std::string name  /* undef if not name */,
                                            AddressSpace &as,
                                            unsigned bytes,
                                            Expr::Width type,
                                            ExecutionState *&oobState,
                                            bool useFZoneConstraints,
                                            bool tryMultiple) {
  assert(dynamic_cast<Heap *>(&as) && "Expected heap address space");

  int fZoneIdx;
  // experimental: if fzones are not involved, let any address pass the heap safety check.
  // Those that are not safe will trigger multiple resolution and an OOB error anyway.
  if (useFZoneConstraints) {
    // sanity check: does the fzone const
    if (!checkHeapSafety(state, address, bytes, useFZoneConstraints, fZoneIdx)) {
      return MemOp_OOB;
    }
  }


  // we could technically convert before checkHeapSafety, but this should avoid creating
  // conversion constraints for stack references.
  if (address->getWidth() != 0) {
    address = convertToInteger(state, address);
  }


  if (useFZoneConstraints) {
    // TODO: refactor. Most resolution-related functions behave differently when fzones are involved.
    // they should just be different functions.
    const ForallZone * fzone = findFZone(state, fZoneIdx);

    // Let's see if the address may resolve outside of the fzone.
    ref<Expr> notInFZone = fzone->getExcludesExpr(address, ConstantExpr::alloc(bytes, Context::get().getPointerWidth()));
    bool success;
    bool solver_success = solver->mustBeFalse(state.getConstraints(/*useHeapConstraints=*/true, true, fZoneIdx), 
      notInFZone, success, state.queryMetaData); 

    // simplify notInFZone since it will be appended to constarint sets without simplification.
    notInFZone = doTpotSimplifications(state, notInFZone);

    ExecutionState *fzoneResState = &state;
    if (!success) {
      // might resolve to other heap objects.
      
      ExecutionState *_oobState = NULL;
      tryMultipleResolution(state, mop, address, value, target, 
                              objSize, name, as, bytes, type, _oobState,
                              /*useHeapConstraints=*/true,
                              useFZoneConstraints, fZoneIdx,
                              notInFZone);
      // assert(oobState && "Expected an oobState");
      if (!_oobState) {
        // This should not happen, since the heapSafety check without fzone constraints
        // would suceed in this case.
        tpot_message("Expected an oobState.. Something is fishy.");
        raise(SIGINT);
        return MemOp_Success;
      }

      // sanity check: resolution must be within fzone in the oob state.
      solver_success = solver->mustBeFalse(_oobState->getConstraints(/*useHeapConstraints=*/true, true, fZoneIdx), 
      notInFZone, success, _oobState->queryMetaData); 
      assert(success);

      fzoneResState = _oobState;
    }

    handleFZoneResolution(*fzoneResState, findFZone(*fzoneResState, fZoneIdx), address, bytes,
      mop, value, target, name, type);

      
    return MemOp_Success;
  }

  LOG_MEMORY_RESOLUTION("Single resolution in heap");
  MemOpResult res;
  res = trySingleResolution(state, mop, address, value, target, 
                          objSize, name, as, bytes, type,
                          /*useHeapConstraints=*/true,
                          useFZoneConstraints, fZoneIdx);
  if (res == MemOp_Success || res == MemOp_Error)
    return res;

  if (!tryMultiple)
    return MemOp_OOB;

  res = tryMultipleResolution(state, mop, address, value, target, 
                          objSize, name, as, bytes, type, oobState,
                          /*useHeapConstraints=*/true,
                          useFZoneConstraints, fZoneIdx);
  return res;
}

void Executor::executeMemoryOperation(ExecutionState &state,
                                      memop_type mop,
                                      ref<Expr> address,
                                      ref<Expr> value /* undef if not write */,
                                      KInstruction *target /* undef if not read */,
                                      Expr::Width objSize  /* undef if not name */,
                                      std::string name  /* undef if not name */) {
  Expr::Width type;
  if (mop == MEMOP_WRITE) 
    type = value->getWidth();
  else if (mop == MEMOP_READ)
    type = getWidthForLLVMType(target->inst->getType());
  else if (mop == MEMOP_NAME)
    type = objSize;
  else
    assert(0 && "Unknown memory operation");

  unsigned bytes = Expr::getMinBytesForWidth(type);

  ExecutionState *oobState = NULL;
  // Check the state havoced by invariants first.
  LOG_MEMORY_RESOLUTION("Resolving in havoced memory.");
  MemOpResult res = resolveInHavocedMem(state, mop, address, value, target, 
                            objSize, name, state.heap, bytes, type, oobState);  
  if (res == MemOp_Success || res == MemOp_Error)
    return;

  // The state where the pointer does not resolve to a havoced object.
  ExecutionState *baseMemState = oobState ? oobState : &state;
  
  // // Try executing in the address space.
  // SYT_PRINT_STEPS("Single resolution in address space.");
  // res = trySingleResolution(*baseMemState, mop, address, value, target, 
  //                           objSize, name, baseMemState->addressSpace, bytes, type);
  // if (res == MemOp_Success || res == MemOp_Error)
  //   return;

  // If that fails, Klee would try multiple resolution.
  // It's more likely that this is a heap access, so try that instead.
  // SYT_PRINT_STEPS("Checking heap safety.");
  if (address->getKind() == Expr::Constant) { // try addressSpace first
    // Try executing in the address space.
    LOG_MEMORY_RESOLUTION("Single resolution in address space.");
    res = trySingleResolution(*baseMemState, mop, address, value, target, 
                              objSize, name, baseMemState->addressSpace, bytes, type);
    if (res == MemOp_Success || res == MemOp_Error)
      return;

    if (resolveInHeap(*baseMemState, mop, address, value, target, 
                              objSize, name, baseMemState->heap, bytes, type, oobState)
                                 == MemOp_Success) {
      return;
    }
  } else { // try heap first
    if (resolveInHeap(*baseMemState, mop, address, value, target, 
                              objSize, name, baseMemState->heap, bytes, type, oobState)
                                 == MemOp_Success) {
      return;
    }

    // Try executing in the address space.
    LOG_MEMORY_RESOLUTION("Single resolution in address space.");
    res = trySingleResolution(*baseMemState, mop, address, value, target, 
                              objSize, name, baseMemState->addressSpace, bytes, type);
    if (res == MemOp_Success || res == MemOp_Error)
      return;

  }
  LOG_MEMORY_RESOLUTION("Checking heap safety (with fZone constraints))");
  if (resolveInHeap(*baseMemState, mop, address, value, target, 
                          objSize, name, baseMemState->heap, bytes, type, oobState,
                          /*useFZoneConstraints=*/ true) == MemOp_Success) {
    return;
  }

  LOG_MEMORY_RESOLUTION("Multiple resolution in address space");
  raise(SIGINT); // multiple resolution
  // Do multiple resolution
  res = tryMultipleResolution(state, mop, address, value, target, objSize, name,
        state.addressSpace, bytes, type, oobState);
  if (res == MemOp_Success || res == MemOp_Error)
    return;
  // result is MemOp_OOB. This is an error.
  terminateStateOnError(*oobState, "memory error: out of bound pointer",
                          StateTerminationType::Ptr,
                          getAddressInfo(*oobState, address));
}

const MemoryObject *Executor::trySingleResolutionNoOp(ExecutionState &state,
                                        ref<Expr> address,
                                        ref<Expr> value /* undef if not write */,
                                        KInstruction *target /* undef if not read */,
                                        Expr::Width objSize  /* undef if not name */,
                                        std::string name  /* undef if not name */,
                                        AddressSpace &as, 
                                        unsigned bytes,
                                        Expr::Width type,
                                        bool useHeapConstraints,
                                        bool useFZoneConstraints,
                                        int fZoneIdx) {
  // This assertion is weird, but let's keep it. 
  // Something has gone horribly wrong if it fails.
  bool isBaseMem = (&as == &state.addressSpace || &as == &state.heap);
  if (!isBaseMem) {
    bool success = false;
    for (auto inv: state.activeInvariants) {
      if (inv.addressSpace == &as || inv.heap == &as) {
        success = true;
        break;
      }
    }
    assert(success && "Invalid address space");
  }

  if (SimplifySymIndices) {
    if (!isa<ConstantExpr>(address))
      address = ConstraintManager::simplifyExpr(state.constraints, address);
  }

  address = optimizer.optimizeExpr(address, true);

  // fast path: single in-bounds resolution
  ObjectPair op;
  bool success = false;

  solver->setTimeout(coreSolverTimeout);
  LOG_MEMORY_RESOLUTION("Calling resolve one");
  // Instead of changing the resolve* API's to add useFZoneConstraints,
  // we just temporarily modify the state's constraints. 
  // This is safe because we are sure that resolve* will not fork the state.
  auto tmp = state.constraints;
  state.constraints = state.getConstraints(useHeapConstraints, useFZoneConstraints, fZoneIdx);
  if (!as.resolveOne(state, solver, address, op, success)) {
    // address = toConstant(state, address, "resolveOne failure");
    // success = as.resolveOne(cast<ConstantExpr>(address), op);
  }
  solver->setTimeout(time::Span());
  state.constraints = tmp;

  if (success) {
    const MemoryObject *mo = op.first;

    if (MaxSymArraySize && mo->size >= MaxSymArraySize) {
      address = toConstant(state, address, "max-sym-array-size");
    }

    ref<Expr> relative_address = address;
    if(mo->uniqueHeapAddress) 
      relative_address = SubExpr::create(address, mo->uniqueHeapAddress);

    ref<Expr> offset = mo->getOffsetExpr(relative_address);
    ref<Expr> check = mo->getBoundsCheckOffset(offset, bytes);
    check = optimizer.optimizeExpr(check, true);

    bool inBounds;
    solver->setTimeout(coreSolverTimeout);
    ConstraintSet c = state.getConstraints(useHeapConstraints, useFZoneConstraints, fZoneIdx);
    LOG_MEMORY_RESOLUTION("Doing bounds check");
    bool success = solver->mustBeTrue(c, check, inBounds,
                                      state.queryMetaData);
    solver->setTimeout(time::Span());
    if (!success) {
      state.pc = state.prevPC;
      terminateStateOnSolverError(state, "Query timed out (bounds check).");
      return NULL;
    }

    if (inBounds) {
      const ForallZone *fzone = dynamic_cast<const ForallZone *>(mo);
      if (useFZoneConstraints && !fzone) {
        raise(SIGINT); // this is very likely a bug
      }

      return mo;
    }
  }
  return NULL;
}


NoOpResolutionList Executor::multipleResolutionNoOp(ExecutionState &state,
                                            ref<Expr> address,
                                            ref<Expr> value /* undef if not write */,
                                            KInstruction *target /* undef if not read */,
                                            Expr::Width objSize  /* undef if not name */,
                                            std::string name  /* undef if not name */,
                                            AddressSpace &as,
                                            unsigned bytes,
                                            Expr::Width type,
                                            ExecutionState *&oobState,
                                            bool useFZoneConstraints,
                                            int fZoneIdx) {
  // TODO: refactor. This is mostly copied from tryMultipleResolution.

  // This assertion is weird, but let's keep it. 
  // Something has gone horribly wrong if it fails.
  bool isBaseMem = (&as == &state.addressSpace || &as == &state.heap);
  if (!isBaseMem) {
    bool success = false;
    for (auto inv: state.activeInvariants) {
      if (inv.addressSpace == &as || inv.heap == &as) {
        success = true;
        break;
      }
    }
    assert(success && "Invalid address space");
  }

  address = optimizer.optimizeExpr(address, true);
  ResolutionList rl;  
  solver->setTimeout(coreSolverTimeout);

  // Instead of changing the resolve* API's to add useFZoneConstraints,
  // we just temporarily modify the state's constraints. 
  // This is safe because we are sure that resolve* will not fork the state.
  auto tmp = state.constraints;
  state.constraints = state.getConstraints(/*useHeapConstraints=*/true, useFZoneConstraints, fZoneIdx);
  bool incomplete = as.resolve(state, solver, address, rl,
                                               0, coreSolverTimeout);
  solver->setTimeout(time::Span());
  
  // XXX there is some query wasteage here. who cares?
  // ExecutionState *unbound = &state;
  NoOpResolutionList result;
  
  ref<Expr> accCond = ConstantExpr::create(1, Expr::Bool);
  Solver::Validity solverRes;

  for (ResolutionList::iterator i = rl.begin(), ie = rl.end(); i != ie; ++i) {
    const MemoryObject *mo = i->first;

    ref<Expr> relative_address = address;
    if(mo->uniqueHeapAddress) 
      relative_address = SubExpr::create(address, mo->uniqueHeapAddress);

    ref<Expr> inBounds = mo->getBoundsCheckPointer(relative_address, bytes);
    
    // StatePair branches = fork(*unbound, inBounds, true, BranchType::MemOp);
    ref<Expr> curCond = AndExpr::create(accCond, inBounds);
    accCond = AndExpr::create(accCond, NotExpr::create(inBounds));

    bool success = solver->evaluate(state.constraints, 
                                  curCond, solverRes,
                                  state.queryMetaData);

    // ExecutionState *bound = branches.first;

    // bound can be 0 on failure or overlapped 
    if (solverRes != Solver::False) {
      result.objects.push_back(std::make_pair(mo, curCond));
    }

    if (solverRes == Solver::True)
      break;
  }
  

  if (solverRes != Solver::True) {
    if (incomplete) {
      terminateStateOnSolverError(state, "Query timed out (resolve).");
    } else {
      assert(false && "Multiple resolution NoOp failed");
    }
  }
  state.constraints = tmp;
  return result;
}

NoOpResolutionList Executor::handleFZoneResolutionNoOp(ExecutionState &state, const ForallZone *fzone, ref<Expr> address, unsigned bytes,
                                     ref<Expr> value /* undef if not write */,
                                     KInstruction *target /* undef if not read */,
                                     std::string name  /* undef if not name */,
                                     Expr::Width type) {
  // We know that address resolves to the fzone and children when forall constraints are used.

  int fZoneIdx = findFZoneIdx(state, fzone);
  // TODO: we compute the offset twice. Remove this.
  ref<Expr> offset = determineOffset(state, address, fZoneIdx);

  // We need to figure out which children this can point to.
  // the structure of this resembles tryMultipleResolution.
  // ExecutionState *unbound = &state;
  NoOpResolutionList result;
  
  ref<Expr> accCond = ConstantExpr::create(1, Expr::Bool);
  Solver::Validity solverRes;

  if (state.heap.fZoneChildren.find(fzone) != state.heap.fZoneChildren.end()) {
    std::vector<const SytSSMemoryObject *> children = state.heap.fZoneChildren[fzone];
    for (auto c : children) {
      // The fzone constraints will not keep address from resolving to the child.
      // So we can check for "may resolve" without fzone constraints.
      if (Heap::mayResolveTo(state, solver, c, address, /*extraConstraints=*/accCond)) {
        // See if the uniqueness of fzone pointers keeps address from resolving to c.
        // TODO
        if (false) {
          continue;
        }

        // We found a child that address may resolve to.
        const MemoryObject *mo = c;

        ref<Expr> relative_address = address;
        if(mo->uniqueHeapAddress) 
          relative_address = SubExpr::create(address, mo->uniqueHeapAddress);

        // ref<Expr> inBounds = mo->getBoundsCheckPointer(relative_address, bytes);
        // ref<Expr> inBounds = EqExpr::create(relative_address, offset);
        //!tmp
        ref<Expr> inBounds = EqExpr::create(BV2IntExpr::getBVForm(relative_address), BV2IntExpr::getBVForm(offset));
        
        // StatePair branches = fork(*unbound, inBounds, true, BranchType::MemOp, /*useHeapConstraints=*/true);
        ref<Expr> curCond = AndExpr::create(accCond, inBounds);
        accCond = AndExpr::create(accCond, NotExpr::create(inBounds));

        bool success = solver->evaluate(state.constraints, 
                                  curCond, solverRes,
                                  state.queryMetaData);

        // ExecutionState *bound = branches.first;

        if (solverRes != Solver::False) {
          result.add(mo, curCond);
        }

        if (solverRes == Solver::True)
          break;
      }
    }
  }

  if (solverRes != Solver::True) {
    result.add(fzone, accCond);
    // executeMemOpInFreshInstance(*unbound, fzone,  mop, address, value, target, name, type);
  }
  return result;
}

NoOpResolutionList Executor::resolveInHeapNoOp(ExecutionState &state,
                                            ref<Expr> address,
                                            ref<Expr> value /* undef if not write */,
                                            KInstruction *target /* undef if not read */,
                                            Expr::Width objSize  /* undef if not name */,
                                            std::string name  /* undef if not name */,
                                            AddressSpace &as,
                                            unsigned bytes,
                                            Expr::Width type,
                                            ExecutionState *&oobState,
                                            bool useFZoneConstraints) {
  assert(dynamic_cast<Heap *>(&as) && "Expected heap address space");

  int fZoneIdx;
  // By using an explicit fzoneIdx and checking for heap safety using one fzone at a time,
  // we give up completeness over examples where a pointer can resolve into one of a number of
  // fzones. For now, this is reasonable but we should make the assumption explicit.

  // example: given names_obj_forall(&arr1[i]) and names_obj_forall(&arr2[i]) and
  // p == arr1[0] || p == arr2[0], we will not be able to resolve p to either arr1 or arr2.

   // experimental: if fzones are not involved, let any address pass the heap safety check.
  // Those that are not safe will trigger multiple resolution and an OOB error anyway.
  if (useFZoneConstraints) {
    if (!checkHeapSafety(state, address, bytes, useFZoneConstraints, fZoneIdx)) {
      // failed, return empty list
      return NoOpResolutionList();
    }
  }

  // we could technically convert before checkHeapSafety, but this should avoid creating
  // conversion constraints for stack references.
  if (address->getWidth() != 0) {
    address = convertToInteger(state, address);
  }

  if (useFZoneConstraints) {
    // TODO: refactor. Most resolution-related functions behave differently when fzones are involved.
    // they should just be different functions.
    const ForallZone * fzone = findFZone(state, fZoneIdx);

    // Let's see if the address may resolve outside of the fzone.
    ref<Expr> notInFZone = fzone->getExcludesExpr(address, ConstantExpr::alloc(bytes, Context::get().getPointerWidth()));
    bool success;
    bool solver_success = solver->mustBeFalse(state.getConstraints(/*useHeapConstraints=*/true, true, fZoneIdx), 
      notInFZone, success, state.queryMetaData); 

    NoOpResolutionList res;
    if (!success) {
      raise(SIGINT); // might resolve to other heap objects.
      // TODO: do multiple resolution assuming notInFZone. Assert that there will be an oobState.
      // TODO: handle FZoneResolution over the oobState.
      assert(0);
    }

    // there is an fzone resolution.
    auto fzoneRes = handleFZoneResolutionNoOp(state, fzone, address, bytes, value, target, name, type);
    res = res.concat(fzoneRes);
    // res.add(fzone, ConstantExpr::create(1, Expr::Bool));
    return res;
  }

  const MemoryObject *resSingle = trySingleResolutionNoOp(state, address, value, target, 
                          objSize, name, as, bytes, type,
                          /*useHeapConstraints=*/true,
                          useFZoneConstraints, fZoneIdx);
  if (resSingle) return NoOpResolutionList(resSingle);
  if (!useFZoneConstraints) {
    // don't try multiple resolution if fzone constraints aren't used.
    return NoOpResolutionList();
  }
  return multipleResolutionNoOp(state, address, value, target, 
                          objSize, name, as, bytes, type, oobState, useFZoneConstraints, fZoneIdx);
}

// TODO: this is mostly copied from executeMemoryOperation. Refactor.
NoOpResolutionList Executor::resolveAddressNoOp(ExecutionState &state,
                                      ref<Expr> address,
                                      ref<Expr> value /* undef if not write */,
                                      KInstruction *target /* undef if not read */,
                                      Expr::Width objSize  /* undef if not name */,
                                      std::string name  /* undef if not name */) {
  Expr::Width type = 1; // resolve with width = 1;

  unsigned bytes = Expr::getMinBytesForWidth(type);

  ExecutionState *oobState = NULL;
  // Check the state havoced by invariants first.
  LOG_MEMORY_RESOLUTION("Resolving in havoced memory.");
  NoOpResolutionList res;
  res = resolveInHavocedMemNoOp(state, address, value, target, 
                            objSize, name, state.heap, bytes, type, oobState);  
  if (!res.empty())
    return res;

  // The state where the pointer does not resolve to a havoced object.
  ExecutionState *baseMemState = oobState ? oobState : &state;

  res = resolveInHeapNoOp(*baseMemState, address, value, target, 
                            objSize, name, baseMemState->heap, bytes, type, oobState);
  if (!res.empty()) {
    return res;
  } else {
    // Try executing in the address space.
    const MemoryObject *resSingle = trySingleResolutionNoOp(*baseMemState, address, value, target, 
                              objSize, name, baseMemState->addressSpace, bytes, type);
    if (resSingle) return NoOpResolutionList(resSingle);

    LOG_MEMORY_RESOLUTION("Checking heap safety (with fZone constraints))");
    res = resolveInHeapNoOp(*baseMemState, address, value, target, 
                            objSize, name, baseMemState->heap, bytes, type, oobState,
                            /*useFZoneConstraints=*/ true);
    assert(!res.empty() && "Could not resolve address");
    return res;
  }
}

NoOpResolutionList Executor::resolveInHavocedMemNoOp(ExecutionState &state,
                                            ref<Expr> address,
                                            ref<Expr> value /* undef if not write */,
                                            KInstruction *target /* undef if not read */,
                                            Expr::Width objSize  /* undef if not name */,
                                            std::string name  /* undef if not name */,
                                            AddressSpace &as,
                                            unsigned bytes,
                                            Expr::Width type,
                                            ExecutionState *&oobState) {
  ExecutionState *curState = &state;
  NoOpResolutionList res;
  for (int i = state.activeInvariants.size() -1;
      i >= 0; i--) {
    Heap *havoced_heap = state.activeInvariants[i].heap;
    AddressSpace *havoced_as = state.activeInvariants[i].addressSpace;

    // For now, we do not support multiple resolution in addressSpace.
    const MemoryObject *resSingle = trySingleResolutionNoOp(*curState, address, value, target, 
                            objSize, name, *havoced_as, bytes, type);
    if (resSingle) return NoOpResolutionList(resSingle);

    ExecutionState *oobState = NULL;
    res = resolveInHeapNoOp(*curState, address, value, target, 
                            objSize, name, *havoced_heap, bytes, type, oobState);
    assert(!oobState);
    if (!res.empty())
      return res;
  }
  // failed. return empty list.
  return NoOpResolutionList();
}

void Executor::executeMakeSymbolic(ExecutionState &state, 
                                   const MemoryObject *mo,
                                   const std::string &name) {
  // Create a new object state for the memory object (instead of a copy).
  if (!replayKTest) {
    // Find a unique name for this array.  First try the original name,
    // or if that fails try adding a unique identifier.
    unsigned id = 0;
    std::string uniqueName = name;
    while (!state.arrayNames.insert(uniqueName).second) {
      uniqueName = name + "_" + llvm::utostr(++id);
    } 

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

    const Array *array = arrayCache.CreateArray(uniqueName, array_size,
      0, 0, domain);
    bindObjectInState(state, mo, false, array);
    state.addSymbolic(mo, array);
    
    std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = 
      seedMap.find(&state);
    if (it!=seedMap.end()) { // In seed mode we need to add this as a
                             // binding.
      for (std::vector<SeedInfo>::iterator siit = it->second.begin(), 
             siie = it->second.end(); siit != siie; ++siit) {
        SeedInfo &si = *siit;
        KTestObject *obj = si.getNextInput(mo, NamedSeedMatching);

        if (!obj) {
          if (ZeroSeedExtension) {
            // TODO: consider bitvec bindings?
            std::vector<unsigned char> &values = si.assignment.arr_bindings[array];
            values = std::vector<unsigned char>(mo->size, '\0');
          } else if (!AllowSeedExtension) {
            terminateStateOnUserError(state, "ran out of inputs during seeding");
            break;
          }
        } else {
          if (obj->numBytes != mo->size &&
              ((!(AllowSeedExtension || ZeroSeedExtension)
                && obj->numBytes < mo->size) ||
               (!AllowSeedTruncation && obj->numBytes > mo->size))) {
	    std::stringstream msg;
	    msg << "replace size mismatch: "
		<< mo->name << "[" << mo->size << "]"
		<< " vs " << obj->name << "[" << obj->numBytes << "]"
		<< " in test\n";

            terminateStateOnUserError(state, msg.str());
            break;
          } else {
            // TODO: consider bitvec bindings?
            std::vector<unsigned char> &values = si.assignment.arr_bindings[array];
            values.insert(values.begin(), obj->bytes, 
                          obj->bytes + std::min(obj->numBytes, mo->size));
            if (ZeroSeedExtension) {
              for (unsigned i=obj->numBytes; i<mo->size; ++i)
                values.push_back('\0');
            }
          }
        }
      }
    }
  } else {
    ObjectState *os = bindObjectInState(state, mo, false);
    if (replayPosition >= replayKTest->numObjects) {
      terminateStateOnUserError(state, "replay count mismatch");
    } else {
      KTestObject *obj = &replayKTest->objects[replayPosition++];
      if (obj->numBytes != mo->size) {
        terminateStateOnUserError(state, "replay size mismatch");
      } else {
        for (unsigned i=0; i<mo->size; i++)
          os->write8(i, obj->bytes[i]);
      }
    }
  }
}

/***/

void Executor::runFunctionAsMain(Function *f,
				 int argc,
				 char **argv,
				 char **envp) {
  std::vector<ref<Expr> > arguments;

  // force deterministic initialization of memory objects
  srand(1);
  srandom(1);
  
  MemoryObject *argvMO = 0;

  // In order to make uclibc happy and be closer to what the system is
  // doing we lay out the environments at the end of the argv array
  // (both are terminated by a null). There is also a final terminating
  // null that uclibc seems to expect, possibly the ELF header?

  int envc;
  for (envc=0; envp[envc]; ++envc) ;

  unsigned NumPtrBytes = Context::get().getPointerWidth() / 8;
  KFunction *kf = kmodule->functionMap[f];
  assert(kf);
  Function::arg_iterator ai = f->arg_begin(), ae = f->arg_end();
  if (ai!=ae) {
    arguments.push_back(ConstantExpr::alloc(argc, Expr::Int32));
    if (++ai!=ae) {
      Instruction *first = &*(f->begin()->begin());
      argvMO =
          memory->allocate((argc + 1 + envc + 1 + 1) * NumPtrBytes,
                           /*isLocal=*/false, /*isGlobal=*/true,
                           /*allocSite=*/first, /*alignment=*/8);

      if (!argvMO)
        klee_error("Could not allocate memory for function arguments");

      arguments.push_back(argvMO->getBaseExpr());

      if (++ai!=ae) {
        uint64_t envp_start = argvMO->address + (argc+1)*NumPtrBytes;
        arguments.push_back(Expr::createPointer(envp_start));

        if (++ai!=ae)
          klee_error("invalid main function (expect 0-3 arguments)");
      }
    }
  }

  ExecutionState *state = new ExecutionState(kmodule->functionMap[f]);

  if (pathWriter) 
    state->pathOS = pathWriter->open();
  if (symPathWriter) 
    state->symPathOS = symPathWriter->open();


  if (statsTracker)
    statsTracker->framePushed(*state, 0);

  assert(arguments.size() == f->arg_size() && "wrong number of arguments");
  for (unsigned i = 0, e = f->arg_size(); i != e; ++i)
    bindArgument(kf, i, *state, arguments[i]);

  if (argvMO) {
    ObjectState *argvOS = bindObjectInState(*state, argvMO, false);

    for (int i=0; i<argc+1+envc+1+1; i++) {
      if (i==argc || i>=argc+1+envc) {
        // Write NULL pointer
        argvOS->write(i * NumPtrBytes, Expr::createPointer(0));
      } else {
        char *s = i<argc ? argv[i] : envp[i-(argc+1)];
        int j, len = strlen(s);

        MemoryObject *arg =
            memory->allocate(len + 1, /*isLocal=*/false, /*isGlobal=*/true,
                             /*allocSite=*/state->pc->inst, /*alignment=*/8);
        if (!arg)
          klee_error("Could not allocate memory for function arguments");
        ObjectState *os = bindObjectInState(*state, arg, false);
        for (j=0; j<len+1; j++)
          os->write8(j, s[j]);

        // Write pointer to newly allocated and initialised argv/envp c-string
        argvOS->write(i * NumPtrBytes, arg->getBaseExpr());
      }
    }
  }
  
  initializeGlobals(*state);

  processTree = std::make_unique<PTree>(state);
  run(*state);
  processTree = nullptr;

  // hack to clear memory objects
  delete memory;
  memory = new MemoryManager(NULL);

  globalObjects.clear();
  globalAddresses.clear();

  if (statsTracker)
    statsTracker->done();
}

/*
 * Can be invoked with an arbitrary number of arguments.
 * TODO: this is based on runFunctionAsMain, refactor to avoid code duplication.
 */
void Executor::runFunctionInSyt(Function *f) {

  // force deterministic initialization of memory objects
  srand(1);
  srandom(1);
  
  KFunction *kf = kmodule->functionMap[f];
  assert(kf);


  ExecutionState *state = new ExecutionState(kmodule->functionMap[f]);

  if (pathWriter) 
    state->pathOS = pathWriter->open();
  if (symPathWriter) 
    state->symPathOS = symPathWriter->open();


  if (statsTracker)
    statsTracker->framePushed(*state, 0);

  const FunctionType *fType = 
        dyn_cast<FunctionType>(cast<PointerType>(f->getType())->getElementType());

  for (unsigned i = 0, e = f->arg_size(); i != e; ++i) {
    Expr::Width paramWidth = getWidthForLLVMType(fType->getParamType(i));
    bindArgument(kf, i, *state, BitVecExpr::create("tpot_arg_"+ std::to_string(i), paramWidth));
  }
  
  initializeGlobals(*state);

  processTree = std::make_unique<PTree>(state);
  run(*state);
  processTree = nullptr;

  // hack to clear memory objects
  delete memory;
  memory = new MemoryManager(NULL);

  globalObjects.clear();
  globalAddresses.clear();

  if (statsTracker)
    statsTracker->done();
}

void Executor::readTPotConfig(std::string filename) {
  std::ifstream config(filename.c_str());
  if (!config.is_open()) {
    klee_warning("Could not open TPot configuration file at %s", filename.c_str());
    return;
  }

  std::string line;
  bool hasInvariantsToUse = false;
  
  if (!std::getline(config, line) || line != "; API functions") {
    klee_error("Invalid TPot configuration file");
    return;
  }
  while (std::getline(config, line)) {
    if (line == "; Invariants to use") {
      hasInvariantsToUse = true;
      break;
    } else if (line[0] == ';') {
      continue;
    }

    llvm::Function *f =kmodule->module->getFunction(line);
    if (!f) {
      klee_error("Could not find function %s in the module", line.c_str());
      return;
    }
    addTpotAPIFunction(f);
  }

  if (hasInvariantsToUse) {
    while (std::getline(config, line)) {
      if (line[0] == ';') {
        continue;
      }

      auto delimiterPos = line.find(": ");
      std::string potName = line.substr(0, delimiterPos);
      std::string invs = line.substr(delimiterPos + 2);

      std::vector<std::string> invNames;
      std::istringstream iss(invs);
      std::string inv;
      while (std::getline(iss, inv, ',')) {
        invNames.push_back(inv);
      }

      addInvariantRestriction(potName, invNames);
    }
  }
}

void Executor::applyInvariantRestrictions(const std::string &mainFnName) {
  if (tpotInvariantRestrictions.find(mainFnName) == tpotInvariantRestrictions.end()) {
    return;
  }

  auto invSet = tpotInvariantRestrictions[mainFnName];
  if (invSet.empty()) return;

  std::vector<llvm::Function*> prunedInvariants;
  for (auto inv: kmodule->sytInvariants) {
    if (invSet.find(inv->getName().str()) != invSet.end()) {
      prunedInvariants.push_back(inv);
    }
  }

  kmodule->sytInvariants = prunedInvariants;
}

unsigned Executor::getPathStreamID(const ExecutionState &state) {
  assert(pathWriter);
  return state.pathOS.getID();
}

unsigned Executor::getSymbolicPathStreamID(const ExecutionState &state) {
  assert(symPathWriter);
  return state.symPathOS.getID();
}

void Executor::getConstraintLog(const ExecutionState &state, std::string &res,
                                Interpreter::LogType logFormat) {

  switch (logFormat) {
  case STP: {
    Query query(state.constraints, ConstantExpr::alloc(0, Expr::Bool));
    char *log = solver->getConstraintLog(query);
    res = std::string(log);
    free(log);
  } break;

  case KQUERY: {
    std::string Str;
    llvm::raw_string_ostream info(Str);
    ExprPPrinter::printConstraints(info, state.constraints);
    res = info.str();
  } break;

  case SMTLIB2: {
    std::string Str;
    llvm::raw_string_ostream info(Str);
    ExprSMTLIBPrinter printer;
    printer.setOutput(info);
    Query query(state.constraints, ConstantExpr::alloc(0, Expr::Bool));
    printer.setQuery(query);
    printer.generateOutput();
    res = info.str();
  } break;

  default:
    klee_warning("Executor::getConstraintLog() : Log format not supported!");
  }
}

bool Executor::getSymbolicSolution(const ExecutionState &state,
                                   std::vector< 
                                   std::pair<std::string,
                                   std::vector<unsigned char> > >
                                   &res) {
  solver->setTimeout(coreSolverTimeout);

  ConstraintSet extendedConstraints(state.constraints);
  ConstraintSet extendedConstraintsHeapOnly(state.constraints_heapOnly);
  ConstraintManager cm(extendedConstraints, extendedConstraintsHeapOnly);

  // Go through each byte in every test case and attempt to restrict
  // it to the constraints contained in cexPreferences.  (Note:
  // usually this means trying to make it an ASCII character (0-127)
  // and therefore human readable. It is also possible to customize
  // the preferred constraints.  See test/Features/PreferCex.c for
  // an example) While this process can be very expensive, it can
  // also make understanding individual test cases much easier.
  for (auto& pi: state.cexPreferences) {
    bool mustBeTrue;
    // Attempt to bound byte to constraints held in cexPreferences
    bool success =
      solver->mustBeTrue(extendedConstraints, Expr::createIsZero(pi),
        mustBeTrue, state.queryMetaData);
    // If it isn't possible to add the condition without making the entire list
    // UNSAT, then just continue to the next condition
    if (!success) break;
    // If the particular constraint operated on in this iteration through
    // the loop isn't implied then add it to the list of constraints.
    if (!mustBeTrue)
      cm.addConstraint(pi);
  }

  std::vector< std::vector<unsigned char> > arr_values;
  std::vector<const Array*> arr_objects;
  std::vector<bitvec_ce_t> bv_values;
  std::vector<const BitVecExpr*> bv_objects;
  std::vector<int_ce_t> int_values;
  std::vector<const IntExpr*> int_objects;
  for (unsigned i = 0; i != state.symbolic_arrays.size(); ++i)
    arr_objects.push_back(state.symbolic_arrays[i].second);
  for (unsigned i = 0; i != state.symbolic_bitvecs.size(); ++i)
    bv_objects.push_back(state.symbolic_bitvecs[i].get());
  for (unsigned i = 0; i != state.symbolic_ints.size(); ++i)
    int_objects.push_back(state.symbolic_ints[i].get());
  bool success = solver->getInitialValues(extendedConstraints, arr_objects, arr_values,
                                          bv_objects, bv_values,
                                          int_objects, int_values,
                                          state.queryMetaData);
  solver->setTimeout(time::Span());
  if (!success) {
    klee_warning("unable to compute initial values (invalid constraints?)!");
    ExprPPrinter::printQuery(llvm::errs(), state.constraints,
                             ConstantExpr::alloc(0, Expr::Bool));
    return false;
  }
  
  for (unsigned i = 0; i != state.symbolic_arrays.size(); ++i)
    res.push_back(std::make_pair(state.symbolic_arrays[i].first->name, arr_values[i]));

  
  for (unsigned i = 0; i != state.symbolic_bitvecs.size(); ++i) {
    // This is a very weird way to print ints. We'll fix test case output later.
    std::string s = std::to_string(bv_values[i]);
    std::vector<unsigned char> v(s.begin(), s.end());
    res.push_back(std::make_pair(state.symbolic_bitvecs[i]->name, v));
  }

  klee_warning("TPot does not print ints yet. Fix this later.");
    
  return true;
}

void Executor::getCoveredLines(const ExecutionState &state,
                               std::map<const std::string*, std::set<unsigned> > &res) {
  res = state.coveredLines;
}

void Executor::doImpliedValueConcretization(ExecutionState &state,
                                            ref<Expr> e,
                                            ref<ConstantExpr> value) {
  abort(); // FIXME: Broken until we sort out how to do the write back.

  if (DebugCheckForImpliedValues)
    ImpliedValue::checkForImpliedValues(solver->solver.get(), e, value);

  ImpliedValueList results;
  ImpliedValue::getImpliedValues(e, value, results);
  for (ImpliedValueList::iterator it = results.begin(), ie = results.end();
       it != ie; ++it) {
    ReadExpr *re = it->first.get();
    
    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(re->index)) {
      // FIXME: This is the sole remaining usage of the Array object
      // variable. Kill me.
      const MemoryObject *mo = 0; //re->updates.root->object;
      const ObjectState *os = state.addressSpace.findObject(mo);

      if (!os) {
        // object has been free'd, no need to concretize (although as
        // in other cases we would like to concretize the outstanding
        // reads, but we have no facility for that yet)
      } else {
        assert(!os->readOnly && 
               "not possible? read only object with static read?");
        ObjectState *wos = state.addressSpace.getWriteable(mo, os);
        wos->write(CE, it->second);
      }
    }
  }
}

Expr::Width Executor::getWidthForLLVMType(llvm::Type *type) const {
  return kmodule->targetData->getTypeSizeInBits(type);
}

size_t Executor::getAllocationAlignment(const llvm::Value *allocSite) const {
  // FIXME: 8 was the previous default. We shouldn't hard code this
  // and should fetch the default from elsewhere.
  const size_t forcedAlignment = 8;
  size_t alignment = 0;
  llvm::Type *type = NULL;
  std::string allocationSiteName(allocSite->getName().str());
  if (const GlobalObject *GO = dyn_cast<GlobalObject>(allocSite)) {
    alignment = GO->getAlignment();
    if (const GlobalVariable *globalVar = dyn_cast<GlobalVariable>(GO)) {
      // All GlobalVariables's have pointer type
      llvm::PointerType *ptrType =
          dyn_cast<llvm::PointerType>(globalVar->getType());
      assert(ptrType && "globalVar's type is not a pointer");
      type = ptrType->getElementType();
    } else {
      type = GO->getType();
    }
  } else if (const AllocaInst *AI = dyn_cast<AllocaInst>(allocSite)) {
    alignment = AI->getAlignment();
    type = AI->getAllocatedType();
  } else if (isa<InvokeInst>(allocSite) || isa<CallInst>(allocSite)) {
    // FIXME: Model the semantics of the call to use the right alignment
#if LLVM_VERSION_CODE >= LLVM_VERSION(8, 0)
    const CallBase &cs = cast<CallBase>(*allocSite);
#else
    llvm::Value *allocSiteNonConst = const_cast<llvm::Value *>(allocSite);
    const CallSite cs(isa<InvokeInst>(allocSiteNonConst)
                          ? CallSite(cast<InvokeInst>(allocSiteNonConst))
                          : CallSite(cast<CallInst>(allocSiteNonConst)));
#endif
    llvm::Function *fn =
        klee::getDirectCallTarget(cs, /*moduleIsFullyLinked=*/true);
    if (fn)
      allocationSiteName = fn->getName().str();

    klee_warning_once(fn != NULL ? fn : allocSite,
                      "Alignment of memory from call \"%s\" is not "
                      "modelled. Using alignment of %zu.",
                      allocationSiteName.c_str(), forcedAlignment);
    alignment = forcedAlignment;
  } else {
    llvm_unreachable("Unhandled allocation site");
  }

  if (alignment == 0) {
    assert(type != NULL);
    // No specified alignment. Get the alignment for the type.
    if (type->isSized()) {
      alignment = kmodule->targetData->getPrefTypeAlignment(type);
    } else {
      klee_warning_once(allocSite, "Cannot determine memory alignment for "
                                   "\"%s\". Using alignment of %zu.",
                        allocationSiteName.c_str(), forcedAlignment);
      alignment = forcedAlignment;
    }
  }

  // Currently we require alignment be a power of 2
  if (!bits64::isPowerOfTwo(alignment)) {
    klee_warning_once(allocSite, "Alignment of %zu requested for %s but this "
                                 "not supported. Using alignment of %zu",
                      alignment, allocSite->getName().str().c_str(),
                      forcedAlignment);
    alignment = forcedAlignment;
  }
  assert(bits64::isPowerOfTwo(alignment) &&
         "Returned alignment must be a power of two");
  return alignment;
}

void Executor::prepareForEarlyExit() {
  if (statsTracker) {
    // Make sure stats get flushed out
    statsTracker->done();
  }
}

/// Returns the errno location in memory
int *Executor::getErrnoLocation(const ExecutionState &state) const {
#if !defined(__APPLE__) && !defined(__FreeBSD__)
  /* From /usr/include/errno.h: it [errno] is a per-thread variable. */
  return __errno_location();
#else
  return __error();
#endif
}


void Executor::dumpPTree() {
  if (!::dumpPTree) return;

  char name[32];
  snprintf(name, sizeof(name),"ptree%08d.dot", (int) stats::instructions);
  auto os = interpreterHandler->openOutputFile(name);
  if (os) {
    processTree->dump(*os);
  }

  ::dumpPTree = 0;
}

void Executor::dumpStates() {
  if (!::dumpStates) return;

  auto os = interpreterHandler->openOutputFile("states.txt");

  if (os) {
    for (ExecutionState *es : states) {
      *os << "(" << es << ",";
      *os << "[";
      auto next = es->stack.begin();
      ++next;
      for (auto sfIt = es->stack.begin(), sf_ie = es->stack.end();
           sfIt != sf_ie; ++sfIt) {
        *os << "('" << sfIt->kf->function->getName().str() << "',";
        if (next == es->stack.end()) {
          *os << es->prevPC->info->line << "), ";
        } else {
          *os << next->caller->info->line << "), ";
          ++next;
        }
      }
      *os << "], ";

      StackFrame &sf = es->stack.back();
      uint64_t md2u = computeMinDistToUncovered(es->pc,
                                                sf.minDistToUncoveredOnReturn);
      uint64_t icnt = theStatisticManager->getIndexedValue(stats::instructions,
                                                           es->pc->info->id);
      uint64_t cpicnt = sf.callPathNode->statistics.getValue(stats::instructions);

      *os << "{";
      *os << "'depth' : " << es->depth << ", ";
      *os << "'queryCost' : " << es->queryMetaData.queryCost << ", ";
      *os << "'coveredNew' : " << es->coveredNew << ", ";
      *os << "'instsSinceCovNew' : " << es->instsSinceCovNew << ", ";
      *os << "'md2u' : " << md2u << ", ";
      *os << "'icnt' : " << icnt << ", ";
      *os << "'CPicnt' : " << cpicnt << ", ";
      *os << "}";
      *os << ")\n";
    }
  }

  ::dumpStates = 0;
}

ref<Expr> Executor::convertToInteger(ExecutionState &state, ref<Expr> bitvec) {
  assert(bitvec->getWidth() == Expr::Int64);

  std::vector<ref<Expr>> unsignedExprs;
  ref<Expr> res = BV2IntExpr::convert(bitvec, unsignedExprs);
  ref<Expr> unsignedConstrs = state.getUnsignedConstraints(unsignedExprs);
  addConstraintGuarded(state, unsignedConstrs);

  res->bvForm = bitvec;
  return res;
}

void Executor::addUninterpretedFunction(llvm::Function *f) {
  // register the function with the SMT solver
  const FunctionType *fType =  dyn_cast<FunctionType>(
      cast<PointerType>(f->getType())->getElementType());
  std::vector<Expr::Width> argTypes;
  for (unsigned i = 0; i < fType->getNumParams(); i++) {
    Type *paramType = fType->getParamType(i);
    argTypes.push_back(getWidthForLLVMType(paramType));
  }
  Expr::Width returnWidth = getWidthForLLVMType(fType->getReturnType());
  addSMTFunc(f->getName().str(), argTypes, returnWidth);

  // register the function with SpecialFunctionHandler
  specialFunctionHandler->uninterpFunctions.push_back(f);
}

///

Interpreter *Interpreter::create(LLVMContext &ctx, const InterpreterOptions &opts,
                                 InterpreterHandler *ih, std::string sytInitConstraints) {
  return new Executor(ctx, opts, ih, sytInitConstraints);
}
