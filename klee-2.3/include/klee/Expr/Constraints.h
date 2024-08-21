//===-- Constraints.h -------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_CONSTRAINTS_H
#define KLEE_CONSTRAINTS_H

#include "klee/Expr/Expr.h"
#include "klee/Solver/Solver.h"

namespace klee {

/// Resembles a set of constraints that can be passed around
///
class ConstraintSet {
  friend class ConstraintManager;

public:
  using constraints_ty = std::vector<ref<Expr>>;
  using iterator = constraints_ty::iterator;
  using const_iterator = constraints_ty::const_iterator;

  using constraint_iterator = const_iterator;

  bool empty() const;
  constraint_iterator begin() const;
  constraint_iterator end() const;
  size_t size() const noexcept;

  explicit ConstraintSet(constraints_ty cs) : constraints(std::move(cs)) {}
  ConstraintSet() = default;

  void push_back(const ref<Expr> &e);

  ConstraintSet join(const ConstraintSet &b) const {
    constraints_ty res = constraints;
    res.insert(res.end(), b.constraints.begin(),
                           b.constraints.end());
    return ConstraintSet(res);
  }


  bool operator==(const ConstraintSet &b) const {
    return constraints == b.constraints;
  }

  constraints_ty constraints;
  // Stores read simplifications that are determined to be safe.
  // This is safe because constraints are never removed from the state, so the simplification 
  // will never become unsafe. 
  mutable std::map<ConcatExpr, ref<Expr>> readSimplCache;
  mutable std::map<ConcatExpr, bool> readSimplKnownFailures;

  // we can't use a map here becasue Expr is an abstract class.
  mutable std::vector<std::pair<ref<Expr>, ref<Expr>>> addressSimplTable;

private:
  // constraints_ty constraints;
};

class ExprVisitor;

/// Manages constraints, e.g. optimisation
class ConstraintManager {
public:
  /// Create constraint manager that modifies constraints
  /// \param constraints
  // explicit ConstraintManager(ConstraintSet &constraints);
  explicit ConstraintManager(ConstraintSet &constraints_bv, ConstraintSet &constraints_int);

  /// Simplify expression expr based on constraints
  /// \param constraints set of constraints used for simplification
  /// \param expr to simplify
  /// \return simplified expression
  static ref<Expr> simplifyExpr(const ConstraintSet &constraints,
                                const ref<Expr> &expr);

  static ref<Expr> simplifyReads(Solver *solver, const ConstraintSet &constraints,
                                 const ref<Expr> &expr);

  static ref<Expr> simplifyAddresses(const ConstraintSet &constraints,
                                const ref<Expr> &expr);

  static ref<Expr> instantiteBV2IntAxioms(Solver *solver, const ConstraintSet &constraints,
                                          const ref<Expr> &e);


  /// Add constraint to the referenced constraint set
  /// \param constraint
  void addConstraint(const ref<Expr> &constraint);

private:
  /// Rewrite set of constraints using the visitor
  /// \param visitor constraint rewriter
  /// \return true iff any constraint has been changed
  bool rewriteConstraints(ExprVisitor &visitor);

  /// Add constraint to the set of constraints
  void addConstraintInternal(const ref<Expr> &constraint);

  void pushConstraints(const ref<Expr> &e);

  ConstraintSet &constraints_bv;
  ConstraintSet &constraints_int;
};

} // namespace klee

#endif /* KLEE_CONSTRAINTS_H */