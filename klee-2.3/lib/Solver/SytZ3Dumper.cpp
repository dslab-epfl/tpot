//===-- Z3Solver.cpp -------------------------------------------*- C++ -*-====//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Config/config.h"
#include "klee/Support/ErrorHandling.h"
#include "klee/Support/FileHandling.h"
#include "klee/Support/OptionCategories.h"

#include <csignal>

#ifdef ENABLE_Z3

#include "SytZ3Dumper.h"

#include "klee/Expr/Constraints.h"
#include "klee/Expr/Assignment.h"
#include "klee/Expr/ExprUtil.h"
#include "klee/Solver/Solver.h"
#include "klee/Solver/SolverImpl.h"
#include "llvm/Support/CommandLine.h"

#include "llvm/Support/ErrorHandling.h"

namespace klee {

  SytZ3Dumper::SytZ3Dumper(std::string _dumpFile, std::string _modifiedDumpFile)
      : builder(new Z3Builder(
            /*autoClearConstructCache=*/false,
            /*z3LogInteractionFileArg=*/NULL)) {
    assert(builder && "unable to create Z3Builder");
    Z3_params solverParameters = Z3_mk_params(builder->ctx);
    Z3_params_inc_ref(builder->ctx, solverParameters);

    solver = Z3_mk_solver(builder->ctx);
    Z3_solver_inc_ref(builder->ctx, solver);
    Z3_solver_set_params(builder->ctx, solver, solverParameters);

    std::string error;
    dumpFile = klee_open_output_file(_dumpFile, error);
    modifiedDumpFile = klee_open_output_file(_modifiedDumpFile, error);
    if (!dumpFile) {
      klee_error("SytZ3 error creating file for dumping Z3 queries: %s",
                  error.c_str());
    }
  }

  SytZ3Dumper::~SytZ3Dumper() {
    Z3_params_dec_ref(builder->ctx, solverParameters);
    Z3_solver_dec_ref(builder->ctx, solver);
    delete builder;
  }

  void SytZ3Dumper::addConstraint(ref<Expr> constraint) {
    Z3_solver_assert(builder->ctx, solver, builder->construct(constraint));
  }

  void SytZ3Dumper::dump() {
    *dumpFile << "; this is a SyT pos-state\n";
    *dumpFile << Z3_solver_to_string(builder->ctx, solver);
    *dumpFile << "(check-sat)\n";
    *dumpFile << "; end Z3 query\n\n";
    dumpFile->flush();

    for (auto constName : modified_fields) {
      *modifiedDumpFile << constName << "\n";
    }
    modifiedDumpFile->flush();
  }

  void SytZ3Dumper::addModifiedField(std::string constName) {
    modified_fields.insert(constName);
  }
}
#endif // ENABLE_Z3
