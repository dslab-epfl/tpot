//===-- Constraints.cpp ---------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Expr/Constraints.h"

#include "klee/Expr/ExprVisitor.h"
#include "klee/Module/KModule.h"
#include "klee/Support/OptionCategories.h"

#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"

#include <map>
#include <signal.h> // SIGINT

using namespace klee;

namespace {
llvm::cl::opt<bool> RewriteEqualities(
    "rewrite-equalities",
    llvm::cl::desc("Rewrite existing constraints when an equality with a "
                   "constant is added (default=true)"),
    llvm::cl::init(true),
    llvm::cl::cat(SolvingCat));
} // namespace

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

class ExprReplaceVisitor2 : public ExprVisitor {
private:
  const std::map< ref<Expr>, ref<Expr> > &replacements;

public:
  explicit ExprReplaceVisitor2(
      const std::map<ref<Expr>, ref<Expr>> &_replacements)
      : ExprVisitor(true), replacements(_replacements) {}

  // We don't want equalitities computed for unbound variables
  // to be used to simplify quantified expressions.
  Action visitForall(const ForallExpr &e) override {
    return Action::skipChildren();
  }
  Action visitExists(const ExistsExpr &e) override {
    return Action::skipChildren();
  }

  Action visitExprPost(const Expr &e) override {
    auto it = replacements.find(ref<Expr>(const_cast<Expr *>(&e)));
    if (it!=replacements.end()) {
      return Action::changeTo(it->second);
    }
    return Action::doChildren();
  }
};


//! copied from ExprPPrinter.cpp and modified.
//? Klee duplicates this function in a few places, too..

// ----------- HELPERS FOR READ SIMPLIFICATION ------------

// TPOT: shortcuts meant to patch the fact that we don't canonicalize
// expresssions involving integers. // TODO unpack why this was necessary.
// returns whether a - b == diff, simplifying constant addition and subtraction
bool subEqualityShortcut(ref<Expr> a, ref<Expr> b, int diff, bool &unknown) {
  // (a1 + a2) - b == diff <=> (a1) - b == diff - a2
  if (const AddExpr *AE = dyn_cast<AddExpr>(a)) {
    if (const ConstantExpr *CE = dyn_cast<ConstantExpr>(AE->right)) {
      return subEqualityShortcut(AE->left, b, diff - CE->getSExtValue(), unknown);
    }
    if (const ConstantExpr *CE = dyn_cast<ConstantExpr>(AE->left)) {
      return subEqualityShortcut(AE->right, b, diff - CE->getSExtValue(), unknown);
    }
  }
  
  // a1 - (b1 + b2) == diff <=> a1 - b1 == diff + b2
  if (const AddExpr *AE = dyn_cast<AddExpr>(b)) {
    if (const ConstantExpr *CE = dyn_cast<ConstantExpr>(AE->right)) {
      return subEqualityShortcut(a, AE->left, diff + CE->getSExtValue(), unknown);
    }
    if (const ConstantExpr *CE = dyn_cast<ConstantExpr>(AE->left)) {
      return subEqualityShortcut(a, AE->right, diff + CE->getSExtValue(), unknown);
    }
  }

  if (const SubExpr *SE = dyn_cast<SubExpr>(a)) {
    // (a1 - a2) - b == diff <=> (a1) - b == diff + a2
    if (const ConstantExpr *CE = dyn_cast<ConstantExpr>(SE->right)) {
      return subEqualityShortcut(SE->left, b, diff + CE->getSExtValue(), unknown);
    }
    // TODO: what if a1 is constant?
  }

  if (const SubExpr *SE = dyn_cast<SubExpr>(b)) {
    // a - (b1 - b2) == diff <=> a - b1 == diff - b2
    if (const ConstantExpr *CE = dyn_cast<ConstantExpr>(SE->right)) {
      return subEqualityShortcut(a, SE->left, diff - CE->getSExtValue(), unknown);
    }
    // TODO: what if b1 is constant?
  }

  if (*a == *b) {
    unknown = false;
    return diff == 0;
  }

  unknown = true;
  return false;
}

bool isReadExprAtOffset(const Expr *e, const ReadExpr *base, ref<Expr> offset) {
  const ReadExpr *re = dyn_cast<ReadExpr>(e);
    
  // right now, all Reads are byte reads but some
  // transformations might change this
  if (!re || (re->getWidth() != Expr::Int8))
    return false;


  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(offset)) {
    bool unknown;
    bool res = subEqualityShortcut(base->index, re->index, CE->getSExtValue(), unknown);
    if (!unknown) {
      return res;
    }
  }
 

  // -------
    
  // Check if the index follows the stride. 
  // FIXME: How aggressive should this be simplified. The
  // canonicalizing builder is probably the right choice, but this
  // is yet another area where we would really prefer it to be
  // global or else use static methods.
  return SubExpr::create(base->index, re->index) == offset;
}

/// hasOrderedReads: \arg e must be a ConcatExpr, \arg stride must
/// be 1 or -1.  
///
/// If all children of this Concat are reads or concats of reads
/// with consecutive offsets according to the given \arg stride, it
/// returns the base ReadExpr according to \arg stride: first Read
/// for 1 (MSB), last Read for -1 (LSB).  Otherwise, it returns
/// null.
const ReadExpr* hasOrderedReads(const Expr *a, int stride, int &numBytes) {
  assert(a->getKind() == Expr::Concat);
  // assert(stride == 1 || stride == -1);
  assert(stride == -1);

  const Expr *eVar = a;
  
  const ReadExpr *base = dyn_cast<ReadExpr>(eVar->getKid(0));
  
  // right now, all Reads are byte reads but some
  // transformations might change this
  if (!base || base->getWidth() != Expr::Int8)
    return NULL;
  
  // Get stride expr in proper index width.
  Expr::Width idxWidth = base->index->getWidth();
  // ref<Expr> strideExpr = ConstantExpr::alloc(stride, idxWidth);

  ref<Expr> offset = ConstantExpr::create(0, idxWidth);
  
  eVar = eVar->getKid(1).get();
  numBytes = 2;
  
  // concat chains are unbalanced to the right
  while (eVar->getKind() == Expr::Concat) {
    offset = AddExpr::create(offset, ConstantExpr::create(1, idxWidth));
    if (!isReadExprAtOffset(eVar->getKid(0).get(), base, offset))
      return NULL;
    
    eVar = eVar->getKid(1).get();
    numBytes++;
  }
  
  offset = AddExpr::create(offset, ConstantExpr::create(1, idxWidth));
  if (!isReadExprAtOffset(eVar, base, offset))
    return NULL;
  
  if (stride == -1)
    return cast<ReadExpr>(eVar);
  else return base;
}

// ----------------------------------------------------


// A solver query per updated byte is a bit too much in terms of overhead.
//#define READSIMPL_PER_UPDATE
// And so is a solver query per byte read
//#define READSIMPL_PER_READ

class ReadSimplifyVisitor : public ExprVisitor {
private:
  const ConstraintSet &constraints;
  Solver *solver;

public:
  explicit ReadSimplifyVisitor(Solver *_solver, const ConstraintSet &_constraints)
      : ExprVisitor(true), solver(_solver) , constraints(_constraints){}

#ifdef READSIMPL_PER_UPDATE
  Action visitRead(const ReadExpr &e) override {
    assert(0 & "this is out of date");
    ref<UpdateNode> cur = e.updates.head;
    std::vector<ref<UpdateNode>> relevantUpdates;
    bool skipped = false;
    while (cur) {
      ref<Expr> overlap = EqExpr::create(e.index, cur->index);
      bool solverRes;
      klee_message("-- trying to simplify read --");
      bool success = solver->mustBeFalse(Query(constraints, overlap), solverRes);
      if (solverRes) {
        // skip this update
        skipped = true;
      } else {
        relevantUpdates.push_back(cur);
      }
      cur = cur->next;
    }
    if (!skipped) {
      return Action::doChildren();
    }

    UpdateList *simpl = new UpdateList(e.updates.root, nullptr);

    for (auto &update : relevantUpdates) {
      simpl->extend(update->index, update->value);
    }

    return Action::changeTo(ReadExpr::alloc(*simpl, e.index));

  }
#else
#ifdef READSIMPL_PER_READ
  Action visitRead(const ReadExpr &e) override {
    if (e.updates.head.isNull()) {
      return Action::doChildren();
    }

    // check if we have a cached simplification
    auto it = constraints.readSimplCache.find(e);
    if (it != constraints.readSimplCache.end()) {
      klee_message("-- readSimplCache hit --");
      if (constraints.readSimplKnownFailures.count(e) > 0) {
        assert(constraints.readSimplKnownFailures[e] == true);
        return Action::doChildren();
      }
      return Action::changeTo(it->second);
    }

    ref<Expr> res = ConstantExpr::create(0, Expr::Bool);
    ref<UpdateNode> cur = e.updates.head;
    while (cur) {
      ref<Expr> overlap = EqExpr::create(e.index, cur->index);
      res = OrExpr::create(res, overlap);
      cur = cur->next;
    }

    bool solverRes;
    klee_message("-- trying to simplify read --");
    bool success = solver->mustBeFalse(Query(constraints, res), solverRes);
    if (!solverRes) {
      constraints.readSimplKnownFailures.insert(std::make_pair(e, false));
      return Action::doChildren();
    }

    UpdateList *simplUL = new UpdateList(e.updates.root, nullptr);
    ref<Expr> simplRead = ReadExpr::create(*simplUL, e.index);

    constraints.readSimplCache.insert(std::make_pair(e, simplRead));
    return Action::changeTo(simplRead);
  }
#else

  Action visitConcat(const ConcatExpr &e) override {
    // We don't account for MSB multibyte reads for now.
    int numBytes;
    const ReadExpr *base = hasOrderedReads(&e, -1, numBytes);
    if (!base || base->updates.head.isNull()) {
      return Action::doChildren();
    }
    assert(numBytes > 0);

    // --- check if we have a cached simplification --- 
    if (constraints.readSimplKnownFailures.count(e) > 0) {
      klee_message("-- readSimplFailure cache hit --");
      assert(constraints.readSimplKnownFailures[e] == true);
      return Action::doChildren();
    }
    auto it = constraints.readSimplCache.find(e);
    if (it != constraints.readSimplCache.end()) {
      klee_message("-- readSimplCache hit --");
      return Action::changeTo(it->second);
    }

    //  --- See if we can ignore all writes ---
    ref<Expr> res = ConstantExpr::create(0, Expr::Bool);
    ref<UpdateNode> cur = base->updates.head;
    while (cur) {
      ref<Expr> overlap = AndExpr::create(
        UleExpr::create(base->index, cur->index),
        UltExpr::create(cur->index, 
          AddExpr::create(base->index, ConstantExpr::create(numBytes, base->index->getWidth()))));

      res = OrExpr::create(res, overlap);
      cur = cur->next;
    }

    bool solverRes;
    LOG_SIMPLIFIER("-- trying to simplify read: ignore all writes --");
    bool success = solver->mustBeFalse(Query(constraints, res), solverRes);
    if (solverRes) {
      UpdateList *simplUL = new UpdateList(base->updates.root, nullptr);
      ref<Expr> simplConcat = ReadExpr::create(*simplUL, base->index);
      for (int i = 1; i < numBytes; i++) {
        simplConcat = ConcatExpr::create(ReadExpr::create(*simplUL, AddExpr::create(base->index, ConstantExpr::create(i, base->index->getWidth()))), simplConcat);
      }
      assert(e.getWidth() == simplConcat->getWidth());
      constraints.readSimplCache.insert(std::make_pair(e, simplConcat));
      return Action::changeTo(simplConcat);
    }


    //  --- See if any group of writes exactly corresponds to the read ---
    // TODO: we need to be able to identify groups of adjacent writes in order
    // to do this properly.. For now let's just assume everything is at an 8-byte granularity.
    int granularity = numBytes;
    assert(granularity >= 2);
    if (granularity != 8) {
      LOG_SIMPLIFIER("Unexpected granularity in read simplification: %d", granularity);
      constraints.readSimplKnownFailures.insert(std::make_pair(e, true));
      return Action::doChildren();
    }

    cur = base->updates.head;
    int curGroupSize = 0;
    ref<Expr> matchesCurGroup = ConstantExpr::create(1, Expr::Bool);
    std::vector<ref<Expr>> curGroupValues;
    while (cur) {
      curGroupSize++;
      ref<Expr> correctByte = EqExpr::create(
        cur->index,
        AddExpr::create(base->index, 
          ConstantExpr::create(granularity - curGroupSize, base->index->getWidth())));

      curGroupValues.push_back(cur->value);

      matchesCurGroup = AndExpr::create(matchesCurGroup, correctByte);
      if (curGroupSize == granularity) {
        bool solverRes;
        LOG_SIMPLIFIER("-- trying to simplify read: exact match --");
        bool success = solver->mustBeTrue(Query(constraints, matchesCurGroup), solverRes);
        if (solverRes) {
          // reconstruct the read
          ref<Expr> simplConcat = curGroupValues[granularity - 1];
          for (int i = granularity - 2; i >= 0; i--) {
            simplConcat = ConcatExpr::create(curGroupValues[i], simplConcat);
          }

          assert(e.getWidth() == simplConcat->getWidth());
          constraints.readSimplCache.insert(std::make_pair(e, simplConcat));
          return Action::changeTo(simplConcat);
        }
        curGroupSize = 0;
        matchesCurGroup = ConstantExpr::create(1, Expr::Bool);
        curGroupValues.clear();
      }

      cur = cur->next;
    }

    // simplification failed.
    constraints.readSimplKnownFailures.insert(std::make_pair(e, true));
    return Action::doChildren();
  }
#endif // READSIMPL_PER_READ
#endif // READSIMPL_PER_UPDATE
};

class AxiomInstVisitor : public ExprVisitor {
private:
  const ConstraintSet &constraints;
  Solver *solver;

ref<Expr> _tryAndPow2(ref<Expr> candidate, ref<Expr> other) {
  // see if we can prove that candidate is a power of two - 1
  ref<Expr> candidatePlusOne = AddExpr::create(candidate, ConstantExpr::create(1, candidate->getWidth()));
  ref<Expr> isPow2 = EqExpr::create(
    AndExpr::create(candidatePlusOne, candidate),
    ConstantExpr::create(0, candidate->getWidth()));
  bool res;
  LOG_SIMPLIFIER("-- trying to instantiate axiom: AndPow2 --");
  bool success = solver->mustBeTrue(Query(constraints, isPow2), res);
  if (res) {
    // we can replace with a modulo
    ref<Expr> mod = URemExpr::create(other, candidatePlusOne);

    // ! ignoring unsignedExprs here
    std::vector<ref<Expr>> unsignedExprs;
    return BV2IntExpr::convert(mod, unsignedExprs);
  }
  return NULL;
}
 
ref<Expr> tryAndPow2(ref<AndExpr>inner) {
  ref<Expr> tryRight = _tryAndPow2(inner->right, inner->left);
  return tryRight.isNull() ? _tryAndPow2(inner->left, inner->right) : tryRight;
}

public:
  explicit AxiomInstVisitor(Solver *_solver, const ConstraintSet &_constraints)
      : ExprVisitor(true), solver(_solver) , constraints(_constraints){}

  Action visitBV2Int(const BV2IntExpr &e) override {
    ref<Expr> inner = e.expr;
    switch (inner->getKind()) {
      case Expr::And: {
        AndExpr *ae = cast<AndExpr>(inner);
        ref<Expr> res = tryAndPow2(ae);
        if (!res.isNull()) {
          return Action::changeTo(res);
        }
        // raise(SIGINT);
        break;
      }
    }
    return Action::doChildren();
  }
};


class AddressSimplifyVisitor : public ExprVisitor {
private:
  const ConstraintSet &constraints;

  ref<Expr> trySimplification(const Expr &e) {
    // TODO: check for constant adds and subtractions

    for (auto &p : constraints.addressSimplTable) {
      if (*(p.first) == e) {
        return p.second;
      }
    }
    return NULL;
  }
public:
  // !
  // construct this visitor with recursion=false (passed to the superclass constuctor)
  // currently, we may get infinite recursion. This can probably be avoided by checking 
  // what goes in the addrSimplTable, but it's not worth the effort right now.
  explicit AddressSimplifyVisitor(const ConstraintSet &_constraints): 
       ExprVisitor(false), constraints(_constraints){}

  Action visitExpr(const Expr &e) override {
    ref<Expr> simpl = trySimplification(e);
    return simpl.isNull() ? Action::doChildren() : Action::changeTo(simpl);
  }

  Action visitExprPost(const Expr &e) override {
    ref<Expr> simpl = trySimplification(e);
    return simpl.isNull() ? Action::doChildren() : Action::changeTo(simpl);
  }
};


bool ConstraintManager::rewriteConstraints(ExprVisitor &visitor) {
  ConstraintSet old_bv;
  bool changed = false;

  std::swap(constraints_bv.constraints, old_bv.constraints);
  for (auto &ce : old_bv) {
    ref<Expr> e = visitor.visit(ce);

    if (e!=ce) {
      addConstraintInternal(e); // enable further reductions
      changed = true;
    } else {
      constraints_bv.push_back(ce);
    }
  }

  ConstraintSet old_int;

  std::swap(constraints_int.constraints, old_int.constraints);
  for (auto &ce : old_int) {
    ref<Expr> e = visitor.visit(ce);

    if (e!=ce) {
      addConstraintInternal(e); // enable further reductions
      changed = true;
    } else {
      constraints_int.push_back(ce);
    }
  }

  return changed;
}

ref<Expr> ConstraintManager::simplifyExpr(const ConstraintSet &constraints,
                                          const ref<Expr> &e) {

  if (isa<ConstantExpr>(e))
    return e;

  std::map< ref<Expr>, ref<Expr> > equalities;

  for (auto &constraint : constraints) {
    if (const EqExpr *ee = dyn_cast<EqExpr>(constraint)) {
      if (isa<ConstantExpr>(ee->left)) {
        equalities.insert(std::make_pair(ee->right,
                                         ee->left));
      } else {
        equalities.insert(
            std::make_pair(constraint, ConstantExpr::alloc(1, Expr::Bool)));
      }
    } else {
      equalities.insert(
          std::make_pair(constraint, ConstantExpr::alloc(1, Expr::Bool)));
    }
  }

  return ExprReplaceVisitor2(equalities).visit(e);
}
// TPot: use the solver to try and simplify reads over objects that are updated
// at indices that provably do not overlap with the read index.
ref<Expr> ConstraintManager::simplifyReads(Solver *solver, const ConstraintSet &constraints,
                                          const ref<Expr> &e) {
  ReadSimplifyVisitor visitor(solver, constraints);
  return visitor.visit(e);
}

ref<Expr> ConstraintManager::instantiteBV2IntAxioms(Solver *solver, const ConstraintSet &constraints,
                                          const ref<Expr> &e) {
  AxiomInstVisitor visitor(solver, constraints);
  return visitor.visit(e);
}

ref<Expr> ConstraintManager::simplifyAddresses(const ConstraintSet &constraints,
                                          const ref<Expr> &e) {
  AddressSimplifyVisitor visitor(constraints);
  return visitor.visit(e);
}

class ConstraintClassifier : public ExprVisitor {
private:
  bool *isIntConstraint;

public:
  ConstraintClassifier(bool *_isIntConstraint) :
    isIntConstraint(_isIntConstraint) {
      *isIntConstraint = false;
    }

  Action visitExpr(const Expr &e) override {
    if (*isIntConstraint) {
      return Action::skipChildren();
    }
    if (e.getWidth() == 1) {
      return Action::doChildren();
    }
    if (e.getWidth() == 0) {
      *isIntConstraint = true;
    }
    return Action::skipChildren();
  }

};

static bool isIntConstraint(const ref<Expr> &e) {
  bool isIntConstraint;
  ConstraintClassifier cc(&isIntConstraint);
  cc.visit(e);
  return isIntConstraint;
}


void ConstraintManager::pushConstraints(const ref<Expr> &e) {
  assert(&constraints_int == &constraints_bv) ;  // tmp. we use a single constraint set now.
  
  bool eDuplicate = false;
  for (auto &c : constraints_bv) {
    if (*c == *e) {
      eDuplicate = true;
    }
  }

  // if (e->skipBV2Int) {
    if (!eDuplicate) {
      constraints_bv.push_back(e);
    }
    return;
  // }
  
  // std::vector<ref<Expr>> unsignedExprs;
  // ref<Expr> b2ic = BV2IntExpr::convertConstraint(e, unsignedExprs);
  // // unsigned constraints should already have been accounted for).

  // // if the constraint already exists, do nothing.
  // bool b2icDuplicate = false;
  // for (auto &c : constraints_int) {
  //   if (*c == *b2ic) {
  //     b2icDuplicate = true;
  //   }
  // }

  // if (*b2ic == *e) {
  //   // assert(isIntConstraint(e));
  //   if (!eDuplicate) {
  //     constraints_int.push_back(e);
  //   }
  //   return;
  // }

  // if (e->getKind() == Expr::Forall || e->exprClass == Expr::FZoneOnly) {
  //   // we never insert forall quantified bitvector constraints.
  //   assert(e->exprClass == Expr::FZoneOnly);
  //   assert(isIntConstraint(e)); 
  //   if (!b2icDuplicate) {
  //     constraints_int.push_back(b2ic);
  //   }
  //   return;
  // }
  

  // if (!eDuplicate) {
  //   constraints_int.push_back(e);
  // }
  // if (!b2icDuplicate) {
  //   constraints_int.push_back(b2ic);
  // }

  // Below was useful when we separated heap constraints (over ints) from data constraints
  // (over bitvectors). We now maintain a single constraint set for both.

  // if (*b2ic == *e) {
  //   assert(isIntConstraint(e));
  //   constraints_int.push_back(e);
  //   return;
  // }

  // if (e->getKind() == Expr::Forall) {
  //   // Try not to produce two quantified statements. Unify instead.
  //   // ref<ForallExpr> fe = cast<ForallExpr>(e);
  //   // ref<ForallExpr> b2ic_fe = cast<ForallExpr>(b2ic);
  //   // assert(fe->var == b2ic_fe->var && "quantified variables do not match");
  //   // ref<Expr> unified = ForallExpr::create(fe->var, AndExpr::create(fe->body, b2ic_fe->body));
  //   // assert(isIntConstraint(unified)); // we never insert forall quantified bitvector constraints.
  //   // constraints_int.push_back(unified);

  //   assert(isIntConstraint(e)); // we never insert forall quantified bitvector constraints.
  //   constraints_int.push_back(b2ic);

  //   return;
  // }

  // if (e->exprClass == Expr::FZoneOnly) {
  //   // only the integer versions of fzone constraints are relevant.
  //   assert(isIntConstraint(e)); // we never insert forall quantified bitvector constraints.
  //   constraints_int.push_back(b2ic);
  //   return;
  // }

  // constraints_bv.push_back(e);
  // // we need int versions of bitvector constraints to reason about aliasing within the same
  // // object.. For instance we need to know (bv2int(order) == 0) given (order == 0).
  // // Pushing this here should at least save us from instering the pure heap constraints into
  // // constraints_bv. (i.e. those that are alreadt over integers).

  // // assert(!isIntConstraint(e)); //.. does not work when disjunctions join int and bv constraints.
  // constraints_bv.push_back(b2ic);


  // constraints_int.push_back(b2ic);
}

void ConstraintManager::addConstraintInternal(const ref<Expr> &e) {
  // rewrite any known equalities and split Ands into different conjuncts

  switch (e->getKind()) {
  case Expr::Constant:
    assert(cast<ConstantExpr>(e)->isTrue() &&
           "attempt to add invalid (false) constraint");
    break;

    // split to enable finer grained independence and other optimizations
  case Expr::And: {
    BinaryExpr *be = cast<BinaryExpr>(e);
    addConstraintInternal(be->left);
    addConstraintInternal(be->right);
    break;
  }

  case Expr::Eq: {
    if (RewriteEqualities) {
      // XXX: should profile the effects of this and the overhead.
      // traversing the constraints looking for equalities is hardly the
      // slowest thing we do, but it is probably nicer to have a
      // ConstraintSet ADT which efficiently remembers obvious patterns
      // (byte-constant comparison).
      BinaryExpr *be = cast<BinaryExpr>(e);
      if (isa<ConstantExpr>(be->left)) {
        ExprReplaceVisitor visitor(be->right, be->left);
        rewriteConstraints(visitor);
      }
    }
    pushConstraints(e);
    break;
  }

  default:
    pushConstraints(e);
    break;
  }
}

void ConstraintManager::addConstraint(const ref<Expr> &e) {
  ref<Expr> simplified = simplifyExpr(constraints_bv.join(constraints_int), e);
  addConstraintInternal(simplified);
}

ConstraintManager::ConstraintManager(ConstraintSet &_constraints_bv, ConstraintSet &_constraints_int)
    : constraints_bv(_constraints_bv), constraints_int(_constraints_int) {}

bool ConstraintSet::empty() const { return constraints.empty(); }

klee::ConstraintSet::constraint_iterator ConstraintSet::begin() const {
  return constraints.begin();
}

klee::ConstraintSet::constraint_iterator ConstraintSet::end() const {
  return constraints.end();
}

size_t ConstraintSet::size() const noexcept { return constraints.size(); }

void ConstraintSet::push_back(const ref<Expr> &e) { constraints.push_back(e); }
