//===-- Z3Solver.h
//---------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_SYTZ3DUMPER_H
#define KLEE_SYTZ3DUMPER_H

#include "klee/Solver/Solver.h"
#include "Z3Builder.h"
#include "llvm/Support/raw_ostream.h"

namespace klee {
/// SytZ3Dumper - based on Z3Solver but only used for tracking and dumping queries.
class SytZ3Dumper {

private:
  Z3_solver solver;
  Z3_params solverParameters;
  std::unique_ptr<llvm::raw_fd_ostream> dumpFile;
  std::unique_ptr<llvm::raw_fd_ostream> modifiedDumpFile;
  std::set<std::string> modified_fields;

  Z3Builder *builder;
  
public:
  SytZ3Dumper(std::string _dumpFile, std::string _modifiedDumpFile);
  ~SytZ3Dumper();

  void addConstraint(ref<Expr> constraint);

  /* dumps the constrints added so far*/
  void dump();

  /* dumps the name of a global variable that changes during execution */
  void addModifiedField(std::string constName);

  //! This is the actual interface we'll use if managing constants
  //! separately pans out performance-wise.
  // void addConstant(char *constName)
  // void invalidateConstant(char *constName)
};
}

#endif /* KLEE_SYTZ3DUMPER_H */
