//===-- Assignment.cpp ----------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Expr/Assignment.h"

namespace klee {

void Assignment::dump() {
  if (arr_bindings.size() == 0) {
    llvm::errs() << "No arr_bindings\n";
    return;
  }
  for (array_bindings_ty::iterator i = arr_bindings.begin(), e = arr_bindings.end(); i != e;
       ++i) {
    llvm::errs() << (*i).first->name << "\n[";
    for (int j = 0, k = (*i).second.size(); j < k; ++j)
      llvm::errs() << (int)(*i).second[j] << ",";
    llvm::errs() << "]\n";
  }

  // TODO: dump bitvec bindings, too.
}

ConstraintSet Assignment::createConstraintsFromAssignment() const {
  ConstraintSet result;
  for (const auto &binding : arr_bindings) {
    const auto &array = binding.first;
    const auto &values = binding.second;

    for (unsigned arrayIndex = 0; arrayIndex < array->size; ++arrayIndex) {
      unsigned char value = values[arrayIndex];
      result.push_back(EqExpr::create(
          ReadExpr::create(UpdateList(array, 0),
                           ConstantExpr::alloc(arrayIndex, array->getDomain())),
          ConstantExpr::alloc(value, array->getRange())));
    }
  }
  return result;
  // TODO: handle bitvec bindings, too.
}
}
