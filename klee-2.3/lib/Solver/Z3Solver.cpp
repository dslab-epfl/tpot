//===-- Z3Solver.cpp -------------------------------------------*- C++ -*-====//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Config/config.h"
#include "klee/Solver/SolverStats.h"
#include "klee/Support/ErrorHandling.h"
#include "klee/Support/FileHandling.h"
#include "klee/Support/OptionCategories.h"

#include <csignal>

#ifdef ENABLE_Z3

#include "Z3Solver.h"
#include "Z3Builder.h"

#include "klee/Expr/Constraints.h"
#include "klee/Expr/Assignment.h"
#include "klee/Expr/ExprUtil.h"
#include "klee/Solver/Solver.h"
#include "klee/Solver/SolverImpl.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include <stdlib.h>
#include <stdio.h>
#include <iostream>
#include <time.h>
#include <sstream>
#include <fstream>
#include <chrono>
#include <fcntl.h>

namespace {
// NOTE: Very useful for debugging Z3 behaviour. These files can be given to
// the z3 binary to replay all Z3 API calls using its `-log` option.
llvm::cl::opt<std::string> Z3LogInteractionFile(
    "debug-z3-log-api-interaction", llvm::cl::init(""),
    llvm::cl::desc("Log API interaction with Z3 to the specified path"),
    llvm::cl::cat(klee::SolvingCat));

llvm::cl::opt<std::string> Z3QueryDumpFile(
    "debug-z3-dump-queries", llvm::cl::init(""),
    llvm::cl::desc("Dump Z3's representation of the query to the specified path"),
    llvm::cl::cat(klee::SolvingCat));

llvm::cl::opt<std::string> Z3CacheFile(
    "use-z3-cache", llvm::cl::init(""),
    llvm::cl::desc("Use a persistent cache for Z3 queries"),
    llvm::cl::cat(klee::SolvingCat));

llvm::cl::opt<std::string> PortfolioPath(
    "solver-portfolio", llvm::cl::init("~/dl/solver-portfolio"),
    llvm::cl::desc("Path to the solver portfolio, containing run-portfolio.sh (default=~/dl/solver-portfolio)"),
    llvm::cl::cat(klee::SolvingCat));

llvm::cl::opt<bool> Z3ValidateModels(
    "debug-z3-validate-models", llvm::cl::init(false),
    llvm::cl::desc("When generating Z3 models validate these against the query"),
    llvm::cl::cat(klee::SolvingCat));

llvm::cl::opt<unsigned>
    Z3VerbosityLevel("debug-z3-verbosity", llvm::cl::init(0),
                     llvm::cl::desc("Z3 verbosity level (default=0)"),
                     llvm::cl::cat(klee::SolvingCat));

llvm::cl::opt<bool>
    Z3PrintSolverTime("debug-z3-solver-time", llvm::cl::init(true),
                      llvm::cl::desc("Log solver time to stderr"),
                      llvm::cl::cat(klee::SolvingCat));

llvm::cl::opt<bool>
    Z3EnableCounterexamples("enable-z3-counterexamples", llvm::cl::init(false),
                            llvm::cl::desc("Enable counterexamples when using Z3 solver (default=false)"),
                            llvm::cl::cat(klee::SolvingCat));
} // namespace

#include "llvm/Support/ErrorHandling.h"


/*
 * This is to exwcute Z3 in a separate process.
 * copied from https://stackoverflow.com/questions/478898/how-do-i-execute-a-command-and-get-the-output-of-the-command-within-c-using-po
 */
#include <cstdio>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <array>

std::string exec(const char* cmd) {
    std::array<char, 128> buffer;
    std::string result;
    std::unique_ptr<FILE, decltype(&pclose)> pipe(popen(cmd, "r"), pclose);
    if (!pipe) {
      assert(0 && "popen() failed!");
    }
    while (fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr) {
        result += buffer.data();
    }
    return result;
}

std::string exec2(const char* cmd1, const char* cmd2) {
    std::array<char, 128> buffer1;
    std::string result1;
    std::array<char, 128> buffer2;
    std::string result2;

    FILE *pipe1 = popen(cmd1, "r");
    if (!pipe1) {
      assert(0 && "popen() failed!");
    }
    FILE *pipe2 = popen(cmd2, "r");
    if (!pipe2) {
      assert(0 && "popen() failed!");
    }

    // make reads non-blocking
    int flags = fcntl(fileno(pipe1), F_GETFL, 0);
    fcntl(fileno(pipe1), F_SETFL, flags | O_NONBLOCK);

    flags = fcntl(fileno(pipe2), F_GETFL, 0);
    fcntl(fileno(pipe2), F_SETFL, flags | O_NONBLOCK);

    while (true) {
      if (fgets(buffer1.data(), buffer1.size(), pipe1) != nullptr) {
        result1 += buffer1.data();
        assert(fgets(buffer1.data(), buffer1.size(), pipe1) == nullptr);
        return result1;
      }
      if (fgets(buffer2.data(), buffer2.size(), pipe2) != nullptr) { 
        result2 += buffer2.data();
        assert(fgets(buffer2.data(), buffer2.size(), pipe2) == nullptr);
        return result2;
      }
    }
}

namespace klee {

static std::map<std::string, std::string> z3Cache;
static bool cacheLoaded = false;

class Z3SolverImpl : public SolverImpl {
private:
  Z3Builder *builder;
  time::Span timeout;
  SolverRunStatus runStatusCode;
  std::unique_ptr<llvm::raw_fd_ostream> dumpedQueriesFile;
  ::Z3_params solverParameters;
  // Parameter symbols
  ::Z3_symbol timeoutParamStrSymbol;
  std::string sytInitConstraintsPath;
  // TODO: add parameters for these two variables
  bool dumpQueries;
  bool useFreshSolver;

  void loadCache();

  bool internalRunSolver(const Query &query,
                        const std::vector<const Array *> *arr_objects,
                        std::vector<std::vector<unsigned char> > *arr_values,
                        const std::vector<const BitVecExpr *> *bv_objects,
                        std::vector<bitvec_ce_t> *bv_values,
                        const std::vector<const IntExpr *> *int_objects,
                        std::vector<int_ce_t> *int_values,
                        bool &hasSolution);

   bool internalRunSolverCounterExample(const Query &query,
                        const std::vector<const Array *> *arr_objects,
                        std::vector<std::vector<unsigned char> > *arr_values,
                        std::vector<bool> *arr_values_ok,
                        const std::vector<const BitVecExpr *> *bv_objects,
                        std::vector<bitvec_ce_t> *bv_values,
                        std::vector<bool> *bv_values_ok,
                        const std::vector<const IntExpr *> *int_objects,
                        std::vector<int_ce_t> *int_values,
                        std::vector<bool> *int_values_ok,
                        bool &hasSolution); 

  bool validateZ3Model(::Z3_solver &theSolver, ::Z3_model &theModel);

public:
  Z3SolverImpl(std::string sytInitConstraintsPath, bool dumpQueries = true, bool useFreshSolver = false);
  ~Z3SolverImpl();

  char *getConstraintLog(const Query &);
  void setCoreSolverTimeout(time::Span _timeout) {
    timeout = _timeout;

    auto timeoutInMilliSeconds = static_cast<unsigned>((timeout.toMicroseconds() / 1000));
    if (!timeoutInMilliSeconds)
      timeoutInMilliSeconds = UINT_MAX;
    Z3_params_set_uint(builder->ctx, solverParameters, timeoutParamStrSymbol,
                       timeoutInMilliSeconds);
  }

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

  bool computeCounterExample(
      const Query &query, const std::vector<const Array *> &arr_objects,
      std::vector<std::vector<unsigned char>> &arr_values,
      std::vector<bool> &arr_values_ok,
      const std::vector<const BitVecExpr *> &bv_objects,
      std::vector<bitvec_ce_t> &bv_values,
      std::vector<bool> &bv_values_ok,
      const std::vector<const IntExpr *> &int_objects,
      std::vector<int_ce_t> &int_values,
      std::vector<bool> &int_values_ok,
      bool &hasSolution) override;

  SolverRunStatus
  handleSolverResponse(::Z3_solver theSolver, ::Z3_lbool satisfiable,
                       const std::vector<const Array *> *arr_objects,
                       std::vector<std::vector<unsigned char> > *arr_values,
                       const std::vector<const BitVecExpr *> *bv_objects,
                       std::vector<bitvec_ce_t> *bv_values,
                       const std::vector<const IntExpr *> *int_objects,
                       std::vector<int_ce_t> *int_values,
                       bool &hasSolution);

  SolverRunStatus
  handleSolverResponseCounterExample(::Z3_solver theSolver, ::Z3_lbool satisfiable,
                      const std::vector<const Array *> *arr_objects,
                      std::vector<std::vector<unsigned char> > *arr_values,
                      std::vector<bool> *arr_values_ok,
                      const std::vector<const BitVecExpr *> *bv_objects,
                      std::vector<bitvec_ce_t> *bv_values,
                      std::vector<bool> *bv_values_ok,
                      const std::vector<const IntExpr *> *int_objects,
                      std::vector<int_ce_t> *int_values,
                      std::vector<bool> *int_values_ok,
                      bool &hasSolution); 

  SolverRunStatus getOperationStatusCode();
};

void Z3SolverImpl::loadCache() {

 clock_t start, end;
  start = clock();
  // read contents of the cache file
  std::ifstream cacheFile;
  cacheFile.open(Z3CacheFile);
  std::string query;
  std::string result;
  while (cacheFile && !cacheFile.eof()) {
    getline(cacheFile, query, ';');
    getline(cacheFile, result, ';');
    z3Cache[query] = result; 
  }
  cacheFile.close();
  end = clock();
    
  double execution_time = ((double)(end - start))/CLOCKS_PER_SEC;
  LOG_SOLVER_TIME("Loading cache took: %f", execution_time);

  cacheLoaded = true;
}

Z3SolverImpl::Z3SolverImpl(std::string sytInitConstraintsPath, bool dumpQueries, bool useFreshSolver)
    : builder(new Z3Builder(
          /*autoClearConstructCache=*/false,
          /*z3LogInteractionFileArg=*/Z3LogInteractionFile.size() > 0
              ? Z3LogInteractionFile.c_str()
              : NULL)),
      runStatusCode(SOLVER_RUN_STATUS_FAILURE),
      sytInitConstraintsPath(sytInitConstraintsPath),
      dumpQueries(dumpQueries),
      useFreshSolver(useFreshSolver) {
  assert(builder && "unable to create Z3Builder");
  solverParameters = Z3_mk_params(builder->ctx);
  Z3_params_inc_ref(builder->ctx, solverParameters);
  timeoutParamStrSymbol = Z3_mk_string_symbol(builder->ctx, "timeout");
  setCoreSolverTimeout(timeout);

  if (!Z3QueryDumpFile.empty() && dumpQueries) {
    std::string error;
    dumpedQueriesFile = klee_open_output_file(Z3QueryDumpFile, error);
    if (!dumpedQueriesFile) {
      klee_error("Error creating file for dumping Z3 queries: %s",
                 error.c_str());
    }
    klee_message("Dumping Z3 queries to \"%s\"", Z3QueryDumpFile.c_str());
  }

  // Set verbosity
  if (Z3VerbosityLevel > 0) {
    std::string underlyingString;
    llvm::raw_string_ostream ss(underlyingString);
    ss << Z3VerbosityLevel;
    ss.flush();
    Z3_global_param_set("verbose", underlyingString.c_str());
  }

  if (!cacheLoaded) {
    loadCache();
  }
}

Z3SolverImpl::~Z3SolverImpl() {
  Z3_params_dec_ref(builder->ctx, solverParameters);
  delete builder;
}

Z3Solver::Z3Solver(std::string sytInitConstraintsPath) : Solver(new Z3SolverImpl(sytInitConstraintsPath)) {}

char *Z3Solver::getConstraintLog(const Query &query) {
  return impl->getConstraintLog(query);
}

void Z3Solver::setCoreSolverTimeout(time::Span timeout) {
  impl->setCoreSolverTimeout(timeout);
}

char *Z3SolverImpl::getConstraintLog(const Query &query) {
  std::vector<Z3ASTHandle> assumptions;
  // We use a different builder here because we don't want to interfere
  // with the solver's builder because it may change the solver builder's
  // cache.
  // NOTE: The builder does not set `z3LogInteractionFile` to avoid conflicting
  // with whatever the solver's builder is set to do.
  Z3Builder temp_builder(/*autoClearConstructCache=*/false,
                         /*z3LogInteractionFile=*/NULL);
  ConstantArrayFinder constant_arrays_in_query;
  for (auto const &constraint : query.constraints) {
    assumptions.push_back(temp_builder.construct(constraint));
    constant_arrays_in_query.visit(constraint);
  }

  // KLEE Queries are validity queries i.e.
  // ∀ X Constraints(X) → query(X)
  // but Z3 works in terms of satisfiability so instead we ask the
  // the negation of the equivalent i.e.
  // ∃ X Constraints(X) ∧ ¬ query(X)
  Z3ASTHandle formula = Z3ASTHandle(
      Z3_mk_not(temp_builder.ctx, temp_builder.construct(query.expr)),
      temp_builder.ctx);
  constant_arrays_in_query.visit(query.expr);

  for (auto const &constant_array : constant_arrays_in_query.results) {
    assert(temp_builder.constant_array_assertions.count(constant_array) == 1 &&
           "Constant array found in query, but not handled by Z3Builder");
    for (auto const &arrayIndexValueExpr :
         temp_builder.constant_array_assertions[constant_array]) {
      assumptions.push_back(arrayIndexValueExpr);
    }
  }

  ::Z3_ast *assumptionsArray = NULL;
  int numAssumptions = assumptions.size();
  if (numAssumptions) {
    assumptionsArray = (::Z3_ast *)malloc(sizeof(::Z3_ast) * numAssumptions);
    for (int index = 0; index < numAssumptions; ++index) {
      assumptionsArray[index] = (::Z3_ast)assumptions[index];
    }
  }

  ::Z3_string result = Z3_benchmark_to_smtlib_string(
      temp_builder.ctx,
      /*name=*/"Emited by klee::Z3SolverImpl::getConstraintLog()",
      /*logic=*/"",
      /*status=*/"unknown",
      /*attributes=*/"",
      /*num_assumptions=*/numAssumptions,
      /*assumptions=*/assumptionsArray,
      /*formula=*/formula);

  if (numAssumptions)
    free(assumptionsArray);

  // We need to trigger a dereference before the `temp_builder` gets destroyed.
  // We do this indirectly by emptying `assumptions` and assigning to
  // `formula`.
  assumptions.clear();
  formula = Z3ASTHandle(NULL, temp_builder.ctx);
  // Client is responsible for freeing the returned C-string
  return strdup(result);
}

bool Z3SolverImpl::computeTruth(const Query &query, bool &isValid) {
  bool hasSolution = false; // to remove compiler warning
  bool status =
      internalRunSolver(query, /*arr_objects=*/NULL, /*arr_values=*/NULL, 
                        /*bv_objects=*/NULL, /*bv_values=*/NULL,
                        /*int_objects=*/NULL, /*int_values=*/NULL, hasSolution);
  isValid = !hasSolution;
  return status;
}

bool Z3SolverImpl::computeValue(const Query &query, ref<Expr> &result) {
  std::vector<const Array *> arr_objects;
  std::vector<const BitVecExpr *> bv_objects;
  std::vector<const IntExpr *> int_objects;
  std::vector<std::vector<unsigned char> > arr_values;
  std::vector<bitvec_ce_t> bv_values;
  std::vector<int_ce_t> int_values;
  bool hasSolution;

  // Find the objects used in the expression, and compute an assignment
  // for them.
  findSymbolicObjects(query.expr, arr_objects, bv_objects, int_objects);
  if (!computeInitialValues(query.withFalse(), arr_objects, arr_values, 
                            bv_objects, bv_values, int_objects, int_values, hasSolution))
    return false;
  assert(hasSolution && "state has invalid constraint set");
  // if (!internalRunSolver(query.withFalse(), &arr_objects, &arr_values, 
  //                           &bv_objects, &bv_values, hasSolution))
  //   return false;
  // assert(hasSolution && "state has invalid constraint set");

  // Evaluate the expression with the computed assignment.
  Assignment a(arr_objects, arr_values, bv_objects, bv_values, int_objects, int_values);
  result = a.evaluate(query.expr);

  return true;
}

bool Z3SolverImpl::computeInitialValues(
    const Query &query,
    const std::vector<const Array *> &arr_objects,
    std::vector<std::vector<unsigned char> > &arr_values,
    const std::vector<const BitVecExpr *> &bv_objects,
    std::vector<bitvec_ce_t> &bv_values,
    const std::vector<const IntExpr *> &int_objects,
    std::vector<int_ce_t> &int_values,
    bool &hasSolution) {
  return internalRunSolver(query, &arr_objects, &arr_values, &bv_objects,
                           &bv_values, &int_objects, &int_values, hasSolution);
}

bool Z3SolverImpl::computeCounterExample(
    const Query &query, const std::vector<const Array *> &arr_objects,
    std::vector<std::vector<unsigned char>> &arr_values,
    std::vector<bool> &arr_values_ok,
    const std::vector<const BitVecExpr *> &bv_objects,
    std::vector<bitvec_ce_t> &bv_values,
    std::vector<bool> &bv_values_ok,
    const std::vector<const IntExpr *> &int_objects,
    std::vector<int_ce_t> &int_values,
    std::vector<bool> &int_values_ok,
    bool &hasSolution) {
  if (Z3EnableCounterexamples) { 
    return internalRunSolverCounterExample(query, &arr_objects, &arr_values, &arr_values_ok,
                                          &bv_objects, &bv_values, &bv_values_ok,
                                          /*
                                          &int_objects, &int_values, &int_values_ok,
                                          */
                                          NULL, NULL, NULL,
                                          hasSolution);
  } else {
    return false;
  }
}

bool Z3SolverImpl::internalRunSolver(
    const Query &query,
    const std::vector<const Array *> *arr_objects,
    std::vector<std::vector<unsigned char> > *arr_values,
    const std::vector<const BitVecExpr *> *bv_objects,
    std::vector<bitvec_ce_t> *bv_values,
    const std::vector<const IntExpr *> *int_objects,
    std::vector<int_ce_t> *int_values,
    bool &hasSolution) {

  if (arr_objects || bv_objects || int_objects) {
    assert(0 && "Some counter examples are broken for now");
  }

  TimerStatIncrementer t(stats::queryTime);
  // NOTE: Z3 will switch to using a slower solver internally if push/pop are
  // used so for now it is likely that creating a new solver each time is the
  // right way to go until Z3 changes its behaviour.
  //
  // TODO: Investigate using a custom tactic as described in
  // https://github.com/klee/klee/issues/653
  Z3_solver theSolver = Z3_mk_solver(builder->ctx);
  Z3_solver_inc_ref(builder->ctx, theSolver);
  Z3_solver_set_params(builder->ctx, theSolver, solverParameters);

  runStatusCode = SOLVER_RUN_STATUS_FAILURE;

  ConstantArrayFinder constant_arrays_in_query;
  for (auto const &constraint : query.constraints) {
    Z3_solver_assert(builder->ctx, theSolver, builder->construct(constraint));
    constant_arrays_in_query.visit(constraint);
  }
  ++stats::queries;
  if (arr_objects || bv_objects)
    ++stats::queryCounterexamples;

  Z3ASTHandle z3QueryExpr =
      Z3ASTHandle(builder->construct(query.expr), builder->ctx);
  constant_arrays_in_query.visit(query.expr);

  for (auto const &constant_array : constant_arrays_in_query.results) {
    assert(builder->constant_array_assertions.count(constant_array) == 1 &&
           "Constant array found in query, but not handled by Z3Builder");
    for (auto const &arrayIndexValueExpr :
         builder->constant_array_assertions[constant_array]) {
      Z3_solver_assert(builder->ctx, theSolver, arrayIndexValueExpr);
    }
  }

  // KLEE Queries are validity queries i.e.
  // ∀ X Constraints(X) → query(X)
  // but Z3 works in terms of satisfiability so instead we ask the
  // negation of the equivalent i.e.
  // ∃ X Constraints(X) ∧ ¬ query(X)
  Z3_solver_assert(
      builder->ctx, theSolver,
      Z3ASTHandle(Z3_mk_not(builder->ctx, z3QueryExpr), builder->ctx));


  unsigned major;
  unsigned minor;
  unsigned build;
  unsigned revision;
  Z3_get_version(&major, &minor, &build, &revision);

  #ifdef USE_OLD_Z3
    // Z3 4.4.1
    Z3_ast sytInitConstraints = NULL;
  #else
    // Z3 4.12.2
    Z3_ast_vector sytInitConstraints;
  #endif

  if (sytInitConstraintsPath != "") {
    klee_warning("Adding sytInitConstraintsPath: %s", sytInitConstraintsPath.c_str());
    sytInitConstraints = Z3_parse_smtlib2_file(builder->ctx, sytInitConstraintsPath.c_str(), 0, 0, 0,
                            0, 0, 0);
#ifdef USE_OLD_Z3
    Z3_inc_ref(builder->ctx, sytInitConstraints);
    Z3_solver_assert(
         builder->ctx, theSolver, sytInitConstraints);
#else
    Z3_ast_vector_inc_ref(builder->ctx, sytInitConstraints);

    unsigned size = Z3_ast_vector_size(builder->ctx, sytInitConstraints);

    // std::cerr << "adding constraints" << std::endl;
    for (unsigned index = 0; index < size; ++index) {
      Z3_solver_assert(
        builder->ctx, theSolver,
          Z3_ast_vector_get(builder->ctx, sytInitConstraints, index));
    }
#endif
  } else {
    // klee_warning("No sytInitConstraintsPath");
  }

  if (dumpedQueriesFile) {
    *dumpedQueriesFile << "; start Z3 query\n";
    *dumpedQueriesFile << Z3_solver_to_string(builder->ctx, theSolver);

    // // Can't forget the magic axiom.
    // *dumpedQueriesFile << "(assert (forall ((a (_ BitVec 64)) (b (_ BitVec 64)))\n";
    // *dumpedQueriesFile << "(=> (not (= a b))\n";
    // *dumpedQueriesFile << "(not (= (tpot_bv2int a) (tpot_bv2int b)))\n";
    // *dumpedQueriesFile << ")))\n";

    *dumpedQueriesFile << "(check-sat)\n";
    *dumpedQueriesFile << "(reset)\n";
    *dumpedQueriesFile << "; end Z3 query\n\n";
    dumpedQueriesFile->flush();
  }

  std::string error;
  std::string curQueryPath = "./cur_query.smt2";
  std::unique_ptr<llvm::raw_fd_ostream> curQueryFile = \
    klee_open_output_file(curQueryPath, error);
  if (!curQueryFile && dumpQueries) {
    klee_warning_once(0, "Error creating file for dumping current Z3 queries: %s",
                error.c_str());
  }

  if (curQueryFile) {
    *curQueryFile << "; start Z3 query\n";
    *curQueryFile << Z3_solver_to_string(builder->ctx, theSolver);

    // // Can't forget the magic axiom.
    // *curQueryFile << "(assert (forall ((a (_ BitVec 64)) (b (_ BitVec 64)))\n";
    // *curQueryFile << "(=> (not (= a b))\n";
    // *curQueryFile << "(not (= (tpot_bv2int a) (tpot_bv2int b)))\n";
    // *curQueryFile << ")))\n";

    *curQueryFile << "(check-sat)\n";
    *curQueryFile << "; end Z3 query\n\n";
    curQueryFile->flush();
  }

  // -------- Z3 Caching ---------
  // Use cache only if we don't need a CE.
  if (!arr_objects && !bv_objects) {
    clock_t start, end;
    start = clock();
    // check if the query is in the cache
    std::string queryStr = Z3_solver_to_string(builder->ctx, theSolver);
    if(z3Cache.count(queryStr)) {
      ++stats::queryCacheHits;
      if (z3Cache[queryStr] == "SAT") {
        hasSolution = true;
      } else if (z3Cache[queryStr] == "UNSAT") {
        hasSolution = false;
      } else {
        klee_error("Error in cache file");
      }
      LOG_SOLVER_TIME("Query found in cache");
      builder->clearConstructCache();
      return true;
    } else {
      ++stats::queryCacheMisses;
    }
    end = clock();
    double execution_time = ((double)(end - start)) / CLOCKS_PER_SEC;
    if (Z3PrintSolverTime && execution_time > 0.05) {
      LOG_SOLVER_TIME("Cache lookup (secs): %f", execution_time);
    }
  }
  // -----------------------------
  


  //! It looks like freshly created solvers are faster than reusing the same one.
  //! I don't know why this is, but a good guess is that builder->ctx carries some
  //! history that is not cleared when the solver is reset, which causes significiant
  //! slowdowns. Let's use the orinigal solver to dump queries, and then parse and solve
  //! them with a fresh solver.
  // ----------------------
#define USE_FRESH_Z3
#define Z3_FRESH_PROCESS

#ifdef USE_FRESH_Z3

if (!Z3EnableCounterexamples) {

#ifdef Z3_FRESH_PROCESS
  auto start = std::chrono::system_clock::now();

  std::string cmd_err_str = PortfolioPath + "/run-portfolio.sh ./cur_query.smt2";
  std::string cmd_str = cmd_err_str + " 2> /dev/null";
  const char *cmd = cmd_str.c_str();
  const char *cmd_err = cmd_err_str.c_str();
  std::string z3Resp = exec(cmd);
  
  // Check for "starts with" rather than equality, in case more than one parallel insance of z3 prints to stdout.
  // TODO: this might still fail if the prints overlap. Implement a better solution.
  if (z3Resp.rfind("sat\n", 0) == 0 ) {
    hasSolution = true;
  } else if (z3Resp.rfind("unsat\n", 0) == 0 ) {
    hasSolution = false;
  } else {
    tpot_message("Unexpected z3 response: %s", z3Resp.c_str());
    tpot_message("Rerunning to capture the error stream");
    tpot_message(exec(cmd_err).c_str());
    klee_error("Unexpected z3 response");
  }
  auto end =  std::chrono::system_clock::now();
  std::chrono::duration<double> elapsed_seconds = end - start;
  // execution_time = ((double)(end - start))/CLOCKS_PER_SEC;
  if (Z3PrintSolverTime) {
    LOG_SOLVER_TIME("Solver time (secs): %f", elapsed_seconds.count());
  }
  // -------- Z3 Caching ---------
  if (elapsed_seconds.count() > 0.2) {
    // write to cache
    std::ofstream cacheFile;
    cacheFile.open(Z3CacheFile, std::ios_base::app);
    cacheFile << Z3_solver_to_string(builder->ctx, theSolver) << ";" << (hasSolution ? "SAT" : "UNSAT") << ";";
    cacheFile.close();
  }
  // -----------------------------
  builder->clearConstructCache();
  return true;
#else // Z3_FRESH_PROCESS
  auto fresh_solver = new Z3SolverImpl(std::string(""), /*dumpQueries=*/ false);
  Z3_solver __theSolver = Z3_mk_solver(fresh_solver->builder->ctx);
  Z3_solver_inc_ref(fresh_solver->builder->ctx, __theSolver);
  Z3_solver_set_params(fresh_solver->builder->ctx, __theSolver, fresh_solver->solverParameters);

  if (curQueryFile) {
    sytInitConstraints = Z3_parse_smtlib2_file(fresh_solver->builder->ctx, curQueryPath.c_str(), 0, 0, 0,
                              0, 0, 0);
  }

  if (sytInitConstraintsPath != "" && sytInitConstraints) {
    #ifdef USE_OLD_Z3
      Z3_inc_ref(fresh_solver->builder->ctx, sytInitConstraints);
      Z3_solver_assert(
          fresh_solver->builder->ctx, __theSolver, sytInitConstraints);
    #else

    Z3_ast_vector_inc_ref(fresh_solver->builder->ctx, sytInitConstraints);
    unsigned size = Z3_ast_vector_size(fresh_solver->builder->ctx, sytInitConstraints);

    for (unsigned index = 0; index < size; ++index) {
      Z3_solver_assert(
        fresh_solver->builder->ctx, __theSolver,
          Z3_ast_vector_get(fresh_solver->builder->ctx, sytInitConstraints, index));
    }
    #endif
  }
  clock_t start, end;
  double execution_time;
  // TODO: fresh solver seems not working during smoke test, it returns wrong values
  if (useFreshSolver) {
      start = clock();
    ::Z3_lbool f_satisfiable = Z3_solver_check(fresh_solver->builder->ctx, __theSolver);
    end = clock();
    execution_time = ((double)(end - start))/CLOCKS_PER_SEC;
    LOG_SOLVER_TIME("Solver time (secs): %f", execution_time);
      runStatusCode = fresh_solver->handleSolverResponse(__theSolver, f_satisfiable, arr_objects, arr_values,
                                        bv_objects, bv_values, int_objects, int_values,
                                        hasSolution);
  } else {
    std::cerr << "calling actual solver" << std::endl;
    start = clock();
    ::Z3_lbool satisfiable = Z3_solver_check(builder->ctx, theSolver);
    end = clock();
    execution_time = ((double)(end - start))/CLOCKS_PER_SEC;
    LOG_SOLVER_TIME("Solver time (secs): %f", execution_time);
    std::cerr << "calling solver response" << std::endl;
    runStatusCode = this->handleSolverResponse(theSolver, satisfiable, arr_objects, arr_values,
                                        bv_objects, bv_values, int_objects, int_values,
                                        hasSolution);
  }
  if (curQueryFile) {
    curQueryFile->close();
  }

  // -------- Z3 Caching ---------
  if (execution_time > 0.2) {
    // write to cache
    std::ofstream cacheFile;
    cacheFile.open(Z3CacheFile, std::ios_base::app);
    cacheFile << Z3_solver_to_string(builder->ctx, theSolver) << ";" << (hasSolution ? "SAT" : "UNSAT") << ";";
    cacheFile.close();
  }
  // -----------------------------

  if (sytInitConstraintsPath != "" && sytInitConstraints) {
#ifdef USE_OLD_Z3
    Z3_dec_ref(fresh_solver->builder->ctx, sytInitConstraints); 
#else
    Z3_ast_vector_dec_ref(fresh_solver->builder->ctx, sytInitConstraints);
#endif
  }
  Z3_solver_dec_ref(fresh_solver->builder->ctx, __theSolver);
  delete fresh_solver;
  // ----------------------
#endif // Z3_FRESH_PROCESS

} else {

  auto fresh_solver = new Z3SolverImpl(std::string(""), /*dumpQueries=*/ false);
  Z3_solver __theSolver = Z3_mk_solver(fresh_solver->builder->ctx);
  Z3_solver_inc_ref(fresh_solver->builder->ctx, __theSolver);
  Z3_solver_set_params(fresh_solver->builder->ctx, __theSolver, fresh_solver->solverParameters);

  if (curQueryFile) {
    sytInitConstraints = Z3_parse_smtlib2_file(fresh_solver->builder->ctx, curQueryPath.c_str(), 0, 0, 0,
                              0, 0, 0);
  }

  if (sytInitConstraintsPath != "" && sytInitConstraints) {
    #ifdef USE_OLD_Z3
      Z3_inc_ref(fresh_solver->builder->ctx, sytInitConstraints);
      Z3_solver_assert(
          fresh_solver->builder->ctx, __theSolver, sytInitConstraints);
    #else

    Z3_ast_vector_inc_ref(fresh_solver->builder->ctx, sytInitConstraints);
    unsigned size = Z3_ast_vector_size(fresh_solver->builder->ctx, sytInitConstraints);

    for (unsigned index = 0; index < size; ++index) {
      Z3_solver_assert(
        fresh_solver->builder->ctx, __theSolver,
          Z3_ast_vector_get(fresh_solver->builder->ctx, sytInitConstraints, index));
    }
    #endif
  }
  clock_t start, end;
  double execution_time;
  // TODO: fresh solver seems not working during smoke test, it returns wrong values
  if (useFreshSolver) {
      start = clock();
    ::Z3_lbool f_satisfiable = Z3_solver_check(fresh_solver->builder->ctx, __theSolver);
    end = clock();
    execution_time = ((double)(end - start))/CLOCKS_PER_SEC;
    LOG_SOLVER_TIME("Solver time (secs): %f", execution_time);
      runStatusCode = fresh_solver->handleSolverResponse(__theSolver, f_satisfiable, arr_objects, arr_values,
                                        bv_objects, bv_values, int_objects, int_values,
                                        hasSolution);
  } else {
    std::cerr << "calling actual solver" << std::endl;
    start = clock();
    ::Z3_lbool satisfiable = Z3_solver_check(builder->ctx, theSolver);
    end = clock();
    execution_time = ((double)(end - start))/CLOCKS_PER_SEC;
    LOG_SOLVER_TIME("Solver time (secs): %f", execution_time);
    std::cerr << "calling solver response" << std::endl;
    runStatusCode = this->handleSolverResponse(theSolver, satisfiable, arr_objects, arr_values,
                                        bv_objects, bv_values, int_objects, int_values,
                                        hasSolution);
  }
  if (curQueryFile) {
    curQueryFile->close();
  }

  // -------- Z3 Caching ---------
  if (execution_time > 0.2) {
    // write to cache
    std::ofstream cacheFile;
    cacheFile.open(Z3CacheFile, std::ios_base::app);
    cacheFile << Z3_solver_to_string(builder->ctx, theSolver) << ";" << (hasSolution ? "SAT" : "UNSAT") << ";";
    cacheFile.close();
  }
  // -----------------------------

  if (sytInitConstraintsPath != "" && sytInitConstraints) {
#ifdef USE_OLD_Z3
    Z3_dec_ref(fresh_solver->builder->ctx, sytInitConstraints); 
#else
    Z3_ast_vector_dec_ref(fresh_solver->builder->ctx, sytInitConstraints);
#endif
  }
  Z3_solver_dec_ref(fresh_solver->builder->ctx, __theSolver);
  delete fresh_solver;
  // ----------------------
}

#else

  std::cerr << "calling actual solver" << std::endl;
  ::Z3_lbool satisfiable = Z3_solver_check(builder->ctx, theSolver);
  std::cerr << "handling response" << std::endl;
  runStatusCode = handleSolverResponse(theSolver, satisfiable, arr_objects, arr_values,
                                       bv_objects, bv_values, int_objects, int_values,
                                       hasSolution);
#endif // USE_FRESH_Z3
// std::cerr << "done.." << std::endl;
  if (sytInitConstraintsPath != "" && sytInitConstraints) {
#ifdef USE_OLD_Z3
      Z3_dec_ref(builder->ctx, sytInitConstraints); 
#else
      Z3_ast_vector_dec_ref(builder->ctx, sytInitConstraints);
#endif
  }
  Z3_solver_dec_ref(builder->ctx, theSolver);
  // Clear the builder's cache to prevent memory usage exploding.
  // By using ``autoClearConstructCache=false`` and clearning now
  // we allow Z3_ast expressions to be shared from an entire
  // ``Query`` rather than only sharing within a single call to
  // ``builder->construct()``.
  builder->clearConstructCache();
  //! Should I clear constructedBitvecs too? Is there much reason to maintain them?

  if (runStatusCode == SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE ||
      runStatusCode == SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE) {
    if (hasSolution) {
      ++stats::queriesInvalid;
    } else {
      ++stats::queriesValid;
    }
    return true; // success
  }
  if (runStatusCode == SolverImpl::SOLVER_RUN_STATUS_INTERRUPTED) {
    raise(SIGINT);
  }
  return false; // failed
}

bool Z3SolverImpl::internalRunSolverCounterExample(
    const Query &query,
    const std::vector<const Array *> *arr_objects,
    std::vector<std::vector<unsigned char> > *arr_values,
    std::vector<bool> *arr_values_ok,
    const std::vector<const BitVecExpr *> *bv_objects,
    std::vector<bitvec_ce_t> *bv_values,
    std::vector<bool> *bv_values_ok,
    const std::vector<const IntExpr *> *int_objects,
    std::vector<int_ce_t> *int_values,
    std::vector<bool> *int_values_ok,
    bool &hasSolution) {

  TimerStatIncrementer t(stats::queryTime);
  // NOTE: Z3 will switch to using a slower solver internally if push/pop are
  // used so for now it is likely that creating a new solver each time is the
  // right way to go until Z3 changes its behaviour.
  //
  // TODO: Investigate using a custom tactic as described in
  // https://github.com/klee/klee/issues/653
  Z3_solver theSolver = Z3_mk_solver(builder->ctx);
  Z3_solver_inc_ref(builder->ctx, theSolver);
  Z3_solver_set_params(builder->ctx, theSolver, solverParameters);

  runStatusCode = SOLVER_RUN_STATUS_FAILURE;

  ConstantArrayFinder constant_arrays_in_query;
  for (auto const &constraint : query.constraints) {
    Z3_solver_assert(builder->ctx, theSolver, builder->construct(constraint));
    constant_arrays_in_query.visit(constraint);
  }
  ++stats::queries;
  if (arr_objects || bv_objects)
    ++stats::queryCounterexamples;

  Z3ASTHandle z3QueryExpr =
      Z3ASTHandle(builder->construct(query.expr), builder->ctx);
  constant_arrays_in_query.visit(query.expr);

  for (auto const &constant_array : constant_arrays_in_query.results) {
    assert(builder->constant_array_assertions.count(constant_array) == 1 &&
           "Constant array found in query, but not handled by Z3Builder");
    for (auto const &arrayIndexValueExpr :
         builder->constant_array_assertions[constant_array]) {
      Z3_solver_assert(builder->ctx, theSolver, arrayIndexValueExpr);
    }
  }

  // KLEE Queries are validity queries i.e.
  // ∀ X Constraints(X) → query(X)
  // but Z3 works in terms of satisfiability so instead we ask the
  // negation of the equivalent i.e.
  // ∃ X Constraints(X) ∧ ¬ query(X)
  Z3_solver_assert(
      builder->ctx, theSolver,
      Z3ASTHandle(Z3_mk_not(builder->ctx, z3QueryExpr), builder->ctx));


  unsigned major;
  unsigned minor;
  unsigned build;
  unsigned revision;
  Z3_get_version(&major, &minor, &build, &revision);

  #ifdef USE_OLD_Z3
    // Z3 4.4.1
    Z3_ast sytInitConstraints = NULL;
  #else
    // Z3 4.12.2
    Z3_ast_vector sytInitConstraints;
  #endif

  if (sytInitConstraintsPath != "") {
    klee_warning("Adding sytInitConstraintsPath: %s", sytInitConstraintsPath.c_str());
    sytInitConstraints = Z3_parse_smtlib2_file(builder->ctx, sytInitConstraintsPath.c_str(), 0, 0, 0,
                            0, 0, 0);
#ifdef USE_OLD_Z3
    Z3_inc_ref(builder->ctx, sytInitConstraints);
    Z3_solver_assert(
         builder->ctx, theSolver, sytInitConstraints);
#else
    Z3_ast_vector_inc_ref(builder->ctx, sytInitConstraints);

    unsigned size = Z3_ast_vector_size(builder->ctx, sytInitConstraints);

    // std::cerr << "adding constraints" << std::endl;
    for (unsigned index = 0; index < size; ++index) {
      Z3_solver_assert(
        builder->ctx, theSolver,
          Z3_ast_vector_get(builder->ctx, sytInitConstraints, index));
    }
#endif
  } else {
    // klee_warning("No sytInitConstraintsPath");
  }

  if (dumpedQueriesFile) {
    *dumpedQueriesFile << "; start Z3 query\n";
    *dumpedQueriesFile << Z3_solver_to_string(builder->ctx, theSolver);
    *dumpedQueriesFile << "(check-sat)\n";
    *dumpedQueriesFile << "(reset)\n";
    *dumpedQueriesFile << "; end Z3 query\n\n";
    dumpedQueriesFile->flush();
  }

  std::string error;
  std::string curQueryPath = "./cur_query.smt2";
  std::unique_ptr<llvm::raw_fd_ostream> curQueryFile = \
    klee_open_output_file(curQueryPath, error);
  if (!curQueryFile && dumpQueries) {
    klee_warning_once(0, "Error creating file for dumping current Z3 queries: %s",
                error.c_str());
  }

  if (curQueryFile) {
    *curQueryFile << "; start Z3 query\n";
    *curQueryFile << Z3_solver_to_string(builder->ctx, theSolver);
    *curQueryFile << "(check-sat)\n";
    *curQueryFile << "; end Z3 query\n\n";
    curQueryFile->flush();
  }

  //! It looks like freshly created solvers are faster than reusing the same one.
  //! I don't know why this is, but a good guess is that builder->ctx carries some
  //! history that is not cleared when the solver is reset, which causes significiant
  //! slowdowns. Let's use the orinigal solver to dump queries, and then parse and solve
  //! them with a fresh solver.
  // ----------------------
#define USE_FRESH_Z3

#ifdef USE_FRESH_Z3
  auto fresh_solver = new Z3SolverImpl(std::string(""), /*dumpQueries=*/ false);
  Z3_solver __theSolver = Z3_mk_solver(fresh_solver->builder->ctx);
  Z3_solver_inc_ref(fresh_solver->builder->ctx, __theSolver);
  Z3_solver_set_params(fresh_solver->builder->ctx, __theSolver, fresh_solver->solverParameters);

  if (curQueryFile) {
    sytInitConstraints = Z3_parse_smtlib2_file(fresh_solver->builder->ctx, curQueryPath.c_str(), 0, 0, 0,
                              0, 0, 0);
  }

  if (sytInitConstraintsPath != "" && sytInitConstraints) {
    #ifdef USE_OLD_Z3
      Z3_inc_ref(fresh_solver->builder->ctx, sytInitConstraints);
      Z3_solver_assert(
          fresh_solver->builder->ctx, __theSolver, sytInitConstraints);
    #else

    Z3_ast_vector_inc_ref(fresh_solver->builder->ctx, sytInitConstraints);
    unsigned size = Z3_ast_vector_size(fresh_solver->builder->ctx, sytInitConstraints);

    for (unsigned index = 0; index < size; ++index) {
      Z3_solver_assert(
        fresh_solver->builder->ctx, __theSolver,
          Z3_ast_vector_get(fresh_solver->builder->ctx, sytInitConstraints, index));
    }
    #endif
  }
  clock_t start, end;
  double execution_time;
  // TODO: fresh solver seems not working during smoke test, it returns wrong values
  if (useFreshSolver) {
      start = clock();
    ::Z3_lbool f_satisfiable = Z3_solver_check(fresh_solver->builder->ctx, __theSolver);
    end = clock();
    execution_time = ((double)(end - start))/CLOCKS_PER_SEC;
    LOG_SOLVER_TIME("Solver time (secs): %f", execution_time);
      runStatusCode = fresh_solver->handleSolverResponseCounterExample(__theSolver, f_satisfiable, arr_objects, arr_values,
                        arr_values_ok, bv_objects, bv_values, bv_values_ok, int_objects, int_values, int_values_ok, hasSolution);
  } else {
    std::cerr << "calling actual solver" << std::endl;
    start = clock();
    ::Z3_lbool satisfiable = Z3_solver_check(builder->ctx, theSolver);
    end = clock();
    execution_time = ((double)(end - start))/CLOCKS_PER_SEC;
    LOG_SOLVER_TIME("Solver time (secs): %f", execution_time);
    std::cerr << "calling solver response" << std::endl;
    runStatusCode = this->handleSolverResponseCounterExample(theSolver, satisfiable, arr_objects, arr_values,
                        arr_values_ok, bv_objects, bv_values, bv_values_ok, int_objects, int_values, int_values_ok, hasSolution);
  }
  if (curQueryFile) {
    curQueryFile->close();
  }

  if (sytInitConstraintsPath != "" && sytInitConstraints) {
#ifdef USE_OLD_Z3
    Z3_dec_ref(fresh_solver->builder->ctx, sytInitConstraints); 
#else
    Z3_ast_vector_dec_ref(fresh_solver->builder->ctx, sytInitConstraints);
#endif
  }
  Z3_solver_dec_ref(fresh_solver->builder->ctx, __theSolver);
  delete fresh_solver;
  // ----------------------
#else

  std::cerr << "calling actual solver" << std::endl;
  ::Z3_lbool satisfiable = Z3_solver_check(builder->ctx, theSolver);
  std::cerr << "handling response" << std::endl;
  runStatusCode = handleSolverResponseCounterExample(__theSolver, satisfiable, arr_objects, arr_values,
                        arr_values_ok, bv_objects, bv_values, bv_values_ok, int_objects, int_values, int_values_ok, hasSolution);
#endif // USE_FRESH_Z3
// std::cerr << "done.." << std::endl;
  if (sytInitConstraintsPath != "" && sytInitConstraints) {
#ifdef USE_OLD_Z3
      Z3_dec_ref(builder->ctx, sytInitConstraints); 
#else
      Z3_ast_vector_dec_ref(builder->ctx, sytInitConstraints);
#endif
  }
  Z3_solver_dec_ref(builder->ctx, theSolver);
  // Clear the builder's cache to prevent memory usage exploding.
  // By using ``autoClearConstructCache=false`` and clearning now
  // we allow Z3_ast expressions to be shared from an entire
  // ``Query`` rather than only sharing within a single call to
  // ``builder->construct()``.
  builder->clearConstructCache();
  //! Should I clear constructedBitvecs too? Is there much reason to maintain them?

  if (runStatusCode == SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE ||
      runStatusCode == SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE) {
    if (hasSolution) {
      ++stats::queriesInvalid;
    } else {
      ++stats::queriesValid;
    }
    return true; // success
  }
  if (runStatusCode == SolverImpl::SOLVER_RUN_STATUS_INTERRUPTED) {
    raise(SIGINT);
  }
  return false; // failed
}

SolverImpl::SolverRunStatus Z3SolverImpl::handleSolverResponse(
    ::Z3_solver theSolver, ::Z3_lbool satisfiable,
    const std::vector<const Array *> *arr_objects,
    std::vector<std::vector<unsigned char> > *arr_values, 
    const std::vector<const BitVecExpr *> *bv_objects,
    std::vector<bitvec_ce_t> *bv_values,
    const std::vector<const IntExpr *> *int_objects,
    std::vector<int_ce_t> *int_values,
    bool &hasSolution) {
  switch (satisfiable) {
  case Z3_L_TRUE: {
    hasSolution = true;
    if (!arr_objects && !bv_objects) {
      // No assignment is needed
      assert(arr_values == NULL && bv_values == NULL);
      return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
    }
    // std::cerr << "getting model" << std::endl;
    ::Z3_model theModel = Z3_solver_get_model(builder->ctx, theSolver);
    // std::cerr << "got model" << std::endl;
    assert(theModel && "Failed to retrieve model");
    Z3_model_inc_ref(builder->ctx, theModel);

    if (arr_objects) {
      assert(arr_values && "values cannot be nullptr");
      arr_values->reserve(arr_objects->size());

      /* Retrieve Array values from the model */
      for (std::vector<const Array *>::const_iterator it = arr_objects->begin(),
                                                      ie = arr_objects->end();
          it != ie; ++it) {
        const Array *array = *it;
        std::vector<unsigned char> data;

        data.reserve(array->size);
        for (unsigned offset = 0; offset < array->size; offset++) {
          // We can't use Z3ASTHandle here so have to do ref counting manually
          ::Z3_ast arrayElementExpr;
          Z3ASTHandle initial_read = builder->getInitialRead(array, offset);

          __attribute__((unused))
          // std::cerr << "calling z3 eval (array)" << std::endl;
          bool successfulEval =
              Z3_model_eval(builder->ctx, theModel, initial_read,
                            /*model_completion=*/Z3_L_TRUE, &arrayElementExpr);
          // std::cerr << "finished z3 eval (array)" << std::endl;
          assert(successfulEval && "Failed to evaluate model");
          Z3_inc_ref(builder->ctx, arrayElementExpr);
          assert(Z3_get_ast_kind(builder->ctx, arrayElementExpr) ==
                    Z3_NUMERAL_AST &&
                "Evaluated expression has wrong sort");

          int arrayElementValue = 0;
          __attribute__((unused))
          bool successGet = Z3_get_numeral_int(builder->ctx, arrayElementExpr,
                                              &arrayElementValue);
          assert(successGet && "failed to get value back");
          assert(arrayElementValue >= 0 && arrayElementValue <= 255 &&
                "Integer from model is out of range");
          data.push_back(arrayElementValue);
          Z3_dec_ref(builder->ctx, arrayElementExpr);
        }
        arr_values->push_back(data);
      }
    }

    if (bv_objects) {
      assert(bv_values && "values cannot be nullptr");
      bv_values->reserve(bv_objects->size());

      /* Retrieve Bitvector values from the model */
      for (std::vector<const BitVecExpr *>::const_iterator it = bv_objects->begin(),
                                                      ie = bv_objects->end();
          it != ie; ++it) {
        const BitVecExpr *bv = *it;
        bitvec_ce_t value;

        ::Z3_ast modelRes;
        // std::cerr << "getting BVHandle" << std::endl;
        Z3ASTHandle bv_z3_handle = builder->getBVHandle(bv->name, bv->width);
        // std::cerr << "got BVHandle" << std::endl;

        // std::cerr << "calling z3 eval" << std::endl;
        __attribute__((unused))
        bool successfulEval =
              Z3_model_eval(builder->ctx, theModel, bv_z3_handle,
                            /*model_completion=*/Z3_L_TRUE, &modelRes);
        assert(successfulEval && "Failed to evaluate model");
        // std::cerr << "finished z3 eval" << std::endl;
        Z3_inc_ref(builder->ctx, modelRes);
        assert(Z3_get_ast_kind(builder->ctx, modelRes) ==
                    Z3_NUMERAL_AST &&
                "Evaluated expression has wrong sort");
        __attribute__((unused))
        bool successGet = Z3_get_numeral_int64(builder->ctx, modelRes,
                                            &value);
        if (!successGet) {
          Z3_string str_res = Z3_get_numeral_string(builder->ctx, modelRes);
          successGet = Z3_get_numeral_uint64(builder->ctx, modelRes,
          #ifdef USE_OLD_Z3
                                            (unsigned long long int *)&value);
          #else
                                            (uint64_t *)&value);
          #endif
          raise(SIGINT);
          assert(successGet && "failed to get value back");
        }
        
        Z3_dec_ref(builder->ctx, modelRes);

        bv_values->push_back(value);
      }
    }

    if (int_objects) {
      assert(int_values && "values cannot be nullptr");
      int_values->reserve(int_objects->size());

      /* Retrieve Int values from the model */
      for (std::vector<const IntExpr *>::const_iterator it = int_objects->begin(),
                                                      ie = int_objects->end();
          it != ie; ++it) {
        const IntExpr *intE = *it;
        int_ce_t value;

        ::Z3_ast modelRes;

        Z3ASTHandle int_z3_handle = builder->intExpr(Z3_mk_string_symbol(builder->ctx, intE->name.c_str()));

        __attribute__((unused))
        bool successfulEval =
              Z3_model_eval(builder->ctx, theModel, int_z3_handle,
                            /*model_completion=*/Z3_L_TRUE, &modelRes);
        assert(successfulEval && "Failed to evaluate model");
        Z3_inc_ref(builder->ctx, modelRes);
        assert(Z3_get_ast_kind(builder->ctx, modelRes) ==
                    Z3_NUMERAL_AST &&
                "Evaluated expression has wrong sort");
        __attribute__((unused))
        bool successGet = Z3_get_numeral_int64(builder->ctx, modelRes,
                                            &value);
        if (!successGet) {
          Z3_string str_res = Z3_get_numeral_string(builder->ctx, modelRes);
          successGet = Z3_get_numeral_uint64(builder->ctx, modelRes,
          #ifdef USE_OLD_Z3
                                            (unsigned long long int *)&value);
          #else
                                            (uint64_t *)&value);
          #endif
          //raise(SIGINT);
          assert(successGet && "failed to get value back");
        }
        
        Z3_dec_ref(builder->ctx, modelRes);

        int_values->push_back(value);
      }
    }

    // Validate the model if requested
    if (Z3ValidateModels) {
      bool success = validateZ3Model(theSolver, theModel);
      if (!success)
        abort();
    }

    Z3_model_dec_ref(builder->ctx, theModel);
    return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
  }
  case Z3_L_FALSE:
    hasSolution = false;
    return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE;
  case Z3_L_UNDEF: {
    ::Z3_string reason =
        ::Z3_solver_get_reason_unknown(builder->ctx, theSolver);
    if (strcmp(reason, "timeout") == 0 || strcmp(reason, "canceled") == 0 ||
        strcmp(reason, "(resource limits reached)") == 0) {
      return SolverImpl::SOLVER_RUN_STATUS_TIMEOUT;
    }
    if (strcmp(reason, "unknown") == 0) {
      return SolverImpl::SOLVER_RUN_STATUS_FAILURE;
    }
    if (strcmp(reason, "interrupted from keyboard") == 0) {
      return SolverImpl::SOLVER_RUN_STATUS_INTERRUPTED;
    }
    klee_warning("Unexpected solver failure. Reason is \"%s,\"\n", reason);
    abort();
  }
  default:
    llvm_unreachable("unhandled Z3 result");
  }
}

SolverImpl::SolverRunStatus Z3SolverImpl::handleSolverResponseCounterExample(
    ::Z3_solver theSolver, ::Z3_lbool satisfiable,
    const std::vector<const Array *> *arr_objects,
    std::vector<std::vector<unsigned char> > *arr_values, 
    std::vector<bool> *arr_values_ok,
    const std::vector<const BitVecExpr *> *bv_objects,
    std::vector<bitvec_ce_t> *bv_values,
    std::vector<bool> *bv_values_ok,
    const std::vector<const IntExpr *> *int_objects,
    std::vector<int_ce_t> *int_values,
    std::vector<bool> *int_values_ok,
    bool &hasSolution) {
  if (int_objects) {
    assert(0 && "Counter examples for int_objects are broken for now");
  }

  switch (satisfiable) {
  case Z3_L_TRUE: {
    hasSolution = true;
    if (!arr_objects && !bv_objects) {
      // No assignment is needed
      assert(arr_values == NULL && bv_values == NULL);
      return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
    }
    // std::cerr << "getting model" << std::endl;
    ::Z3_model theModel = Z3_solver_get_model(builder->ctx, theSolver);
    // std::cerr << "got model" << std::endl;
    assert(theModel && "Failed to retrieve model");
    Z3_model_inc_ref(builder->ctx, theModel);

    if (arr_objects) {
      assert(arr_values && "values cannot be nullptr");
      assert(arr_values_ok && "values_ok cannot be nullptr");
      arr_values->reserve(arr_objects->size());
      arr_values_ok->reserve(arr_objects->size());

      /* Retrieve Array values from the model */
      for (std::vector<const Array *>::const_iterator it = arr_objects->begin(),
                                                      ie = arr_objects->end();
          it != ie; ++it) {
        const Array *array = *it;
        std::vector<unsigned char> data;

        data.reserve(array->size);
        for (unsigned offset = 0; offset < array->size; offset++) {
          // We can't use Z3ASTHandle here so have to do ref counting manually
          ::Z3_ast arrayElementExpr;
          Z3ASTHandle initial_read = builder->getInitialRead(array, offset);

          __attribute__((unused))
          // std::cerr << "calling z3 eval (array)" << std::endl;
          bool successfulEval =
              Z3_model_eval(builder->ctx, theModel, initial_read,
                            /*model_completion=*/Z3_L_TRUE, &arrayElementExpr);
          // std::cerr << "finished z3 eval (array)" << std::endl;
          
          // assert(successfulEval && "Failed to evaluate model");
          if (!successfulEval) goto not_ok_arr;
          
          Z3_inc_ref(builder->ctx, arrayElementExpr);

          // assert(Z3_get_ast_kind(builder->ctx, arrayElementExpr) ==
          //           Z3_NUMERAL_AST &&
          //       "Evaluated expression has wrong sort");
          if (Z3_get_ast_kind(builder->ctx, arrayElementExpr) != Z3_NUMERAL_AST) goto not_ok_arr;

          int arrayElementValue = 0;
          __attribute__((unused))
          bool successGet = Z3_get_numeral_int(builder->ctx, arrayElementExpr,
                                              &arrayElementValue);

          // assert(successGet && "failed to get value back");
          if (!successGet) goto not_ok_arr;

          // assert(arrayElementValue >= 0 && arrayElementValue <= 255 &&
          //       "Integer from model is out of range");
          if (arrayElementValue < 0 || arrayElementValue > 255) goto not_ok_arr;

          data.push_back(arrayElementValue);
          Z3_dec_ref(builder->ctx, arrayElementExpr);
        }

        arr_values->push_back(data);
        arr_values_ok->push_back(true);
        continue;

not_ok_arr:
        arr_values->push_back(data);
        arr_values_ok->push_back(false);
      }
    }

    if (bv_objects) {
      assert(bv_values && "values cannot be nullptr");
      assert(bv_values_ok && "values_ok cannot be nullptr");
      bv_values->reserve(bv_objects->size());
      bv_values_ok->reserve(bv_objects->size());

      /* Retrieve Bitvector values from the model */
      for (std::vector<const BitVecExpr *>::const_iterator it = bv_objects->begin(),
                                                      ie = bv_objects->end();
          it != ie; ++it) {
        const BitVecExpr *bv = *it;
        bitvec_ce_t value;
        __attribute__((unused)) bool successGet;

        ::Z3_ast modelRes;
        // std::cerr << "getting BVHandle" << std::endl;
        Z3ASTHandle bv_z3_handle = builder->getBVHandle(bv->name, bv->width);
        // std::cerr << "got BVHandle" << std::endl;

        // std::cerr << "calling z3 eval" << std::endl;
        __attribute__((unused))
        bool successfulEval =
              Z3_model_eval(builder->ctx, theModel, bv_z3_handle,
                            /*model_completion=*/Z3_L_TRUE, &modelRes);

        // assert(successfulEval && "Failed to evaluate model");
        if (!successfulEval) goto not_ok_bv;

        // std::cerr << "finished z3 eval" << std::endl;
        Z3_inc_ref(builder->ctx, modelRes);

        // assert(Z3_get_ast_kind(builder->ctx, modelRes) ==
        //             Z3_NUMERAL_AST &&
        //         "Evaluated expression has wrong sort");
        if (Z3_get_ast_kind(builder->ctx, modelRes) != Z3_NUMERAL_AST) goto not_ok_bv;
        
        successGet = Z3_get_numeral_int64(builder->ctx, modelRes,
                                            &value);
        if (!successGet) {
          Z3_string str_res = Z3_get_numeral_string(builder->ctx, modelRes);
          successGet = Z3_get_numeral_uint64(builder->ctx, modelRes,
          #ifdef USE_OLD_Z3
                                            (unsigned long long int *)&value);
          #else
                                            (uint64_t *)&value);
          #endif
          // raise(SIGINT);

          // assert(successGet && "failed to get value back");
          if (!successGet) goto not_ok_bv;
        }
        
        Z3_dec_ref(builder->ctx, modelRes);

        bv_values->push_back(value);
        bv_values_ok->push_back(true);
        continue;

not_ok_bv:
        bv_values->push_back(value);
        bv_values_ok->push_back(false);
      }
    }

    if (int_objects) {
      assert(int_values && "values cannot be nullptr");
      int_values->reserve(int_objects->size());

      /* Retrieve Int values from the model */
      for (std::vector<const IntExpr *>::const_iterator it = int_objects->begin(),
                                                      ie = int_objects->end();
          it != ie; ++it) {
        const IntExpr *intE = *it;
        int_ce_t value;

        ::Z3_ast modelRes;

        Z3ASTHandle int_z3_handle = builder->intExpr(Z3_mk_string_symbol(builder->ctx, intE->name.c_str()));

        __attribute__((unused))
        bool successfulEval =
              Z3_model_eval(builder->ctx, theModel, int_z3_handle,
                            /*model_completion=*/Z3_L_TRUE, &modelRes);
        assert(successfulEval && "Failed to evaluate model");
        Z3_inc_ref(builder->ctx, modelRes);
        assert(Z3_get_ast_kind(builder->ctx, modelRes) ==
                    Z3_NUMERAL_AST &&
                "Evaluated expression has wrong sort");
        __attribute__((unused))
        bool successGet = Z3_get_numeral_int64(builder->ctx, modelRes,
                                            &value);
        if (!successGet) {
          Z3_string str_res = Z3_get_numeral_string(builder->ctx, modelRes);
          successGet = Z3_get_numeral_uint64(builder->ctx, modelRes,
          #ifdef USE_OLD_Z3
                                            (unsigned long long int *)&value);
          #else
                                            (uint64_t *)&value);
          #endif
          //raise(SIGINT);
          assert(successGet && "failed to get value back");
        }
        
        Z3_dec_ref(builder->ctx, modelRes);

        int_values->push_back(value);
      }
    }

    // Validate the model if requested
    if (Z3ValidateModels) {
      bool success = validateZ3Model(theSolver, theModel);
      if (!success)
        abort();
    }

    Z3_model_dec_ref(builder->ctx, theModel);
    return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
  }
  case Z3_L_FALSE:
    hasSolution = false;
    return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE;
  case Z3_L_UNDEF: {
    ::Z3_string reason =
        ::Z3_solver_get_reason_unknown(builder->ctx, theSolver);
    if (strcmp(reason, "timeout") == 0 || strcmp(reason, "canceled") == 0 ||
        strcmp(reason, "(resource limits reached)") == 0) {
      return SolverImpl::SOLVER_RUN_STATUS_TIMEOUT;
    }
    if (strcmp(reason, "unknown") == 0) {
      return SolverImpl::SOLVER_RUN_STATUS_FAILURE;
    }
    if (strcmp(reason, "interrupted from keyboard") == 0) {
      return SolverImpl::SOLVER_RUN_STATUS_INTERRUPTED;
    }
    klee_warning("Unexpected solver failure. Reason is \"%s,\"\n", reason);
    abort();
  }
  default:
    llvm_unreachable("unhandled Z3 result");
  }
}

bool Z3SolverImpl::validateZ3Model(::Z3_solver &theSolver, ::Z3_model &theModel) {
  bool success = true;
  ::Z3_ast_vector constraints =
      Z3_solver_get_assertions(builder->ctx, theSolver);
  Z3_ast_vector_inc_ref(builder->ctx, constraints);

  unsigned size = Z3_ast_vector_size(builder->ctx, constraints);

  for (unsigned index = 0; index < size; ++index) {
    Z3ASTHandle constraint = Z3ASTHandle(
        Z3_ast_vector_get(builder->ctx, constraints, index), builder->ctx);

    ::Z3_ast rawEvaluatedExpr;
    __attribute__((unused))
    bool successfulEval =
        Z3_model_eval(builder->ctx, theModel, constraint,
                      /*model_completion=*/Z3_L_TRUE, &rawEvaluatedExpr);
    assert(successfulEval && "Failed to evaluate model");

    // Use handle to do ref-counting.
    Z3ASTHandle evaluatedExpr(rawEvaluatedExpr, builder->ctx);

    Z3SortHandle sort =
        Z3SortHandle(Z3_get_sort(builder->ctx, evaluatedExpr), builder->ctx);
    assert(Z3_get_sort_kind(builder->ctx, sort) == Z3_BOOL_SORT &&
           "Evaluated expression has wrong sort");

    Z3_lbool evaluatedValue =
        Z3_get_bool_value(builder->ctx, evaluatedExpr);
    if (evaluatedValue != Z3_L_TRUE) {
      llvm::errs() << "Validating model failed:\n"
                   << "The expression:\n";
      constraint.dump();
      llvm::errs() << "evaluated to \n";
      evaluatedExpr.dump();
      llvm::errs() << "But should be true\n";
      success = false;
    }
  }

  if (!success) {
    llvm::errs() << "Solver state:\n" << Z3_solver_to_string(builder->ctx, theSolver) << "\n";
    llvm::errs() << "Model:\n" << Z3_model_to_string(builder->ctx, theModel) << "\n";
  }

  Z3_ast_vector_dec_ref(builder->ctx, constraints);
  return success;
}

SolverImpl::SolverRunStatus Z3SolverImpl::getOperationStatusCode() {
  return runStatusCode;
}
}
#endif // ENABLE_Z3
