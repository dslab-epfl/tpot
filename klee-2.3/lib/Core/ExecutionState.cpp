//===-- ExecutionState.cpp ------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "ExecutionState.h"

#include "Memory.h"

#include "klee/Expr/Expr.h"
#include "klee/Module/Cell.h"
#include "klee/Module/InstructionInfoTable.h"
#include "klee/Module/KInstruction.h"
#include "klee/Module/KModule.h"
#include "klee/Support/Casting.h"
#include "klee/Support/OptionCategories.h"

#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include <cassert>
#include <iomanip>
#include <map>
#include <set>
#include <sstream>
#include <stdarg.h>

using namespace llvm;
using namespace klee;

namespace {
cl::opt<bool> DebugLogStateMerge(
    "debug-log-state-merge", cl::init(false),
    cl::desc("Debug information for underlying state merging (default=false)"),
    cl::cat(MergeCat));
}

/***/

std::uint32_t ExecutionState::nextID = 1;

/***/

StackFrame::StackFrame(KInstIterator _caller, KFunction *_kf)
  : caller(_caller), kf(_kf), callPathNode(0), 
    minDistToUncoveredOnReturn(0), varargs(0) {
  locals = new Cell[kf->numRegisters];
}

StackFrame::StackFrame(const StackFrame &s) 
  : caller(s.caller),
    kf(s.kf),
    callPathNode(s.callPathNode),
    allocas(s.allocas),
    minDistToUncoveredOnReturn(s.minDistToUncoveredOnReturn),
    varargs(s.varargs) {
  locals = new Cell[s.kf->numRegisters];
  for (unsigned i=0; i<s.kf->numRegisters; i++)
    locals[i] = s.locals[i];
}

StackFrame::~StackFrame() { 
  delete[] locals; 
}

/***/

ExecutionState::ExecutionState(KFunction *kf)
    : pc(kf->instructions), prevPC(pc) {
  pushFrame(nullptr, kf);
  setID();
  heap.heap_end = IntExpr::create("heap_start");
  syt_stage = ASSUME_INVARIANTS;
}

ExecutionState::~ExecutionState() {
  for (const auto &cur_mergehandler: openMergeStack){
    cur_mergehandler->removeOpenState(this);
  }

  while (!stack.empty()) popFrame();
}

ExecutionState::ExecutionState(const ExecutionState& state):
    pc(state.pc),
    prevPC(state.prevPC),
    stack(state.stack),
    incomingBBIndex(state.incomingBBIndex),
    depth(state.depth),
    addressSpace(state.addressSpace),
    heap(state.heap),

    lambdaParent(state.lambdaParent),
    nameParentsObjects(state.nameParentsObjects),
    lambdaPurpose(state.lambdaPurpose),
    lambdaFunction(state.lambdaFunction),

    instantiatedFEPs(state.instantiatedFEPs),
    multipleResHistory(state.multipleResHistory),

    computeOldValues(state.computeOldValues),
    knownUnsignedExprs(state.knownUnsignedExprs),

    constraints(state.constraints),
    constraints_heapOnly(state.constraints_heapOnly),
    constraints_fZoneOnly(state.constraints_fZoneOnly),
    pathOS(state.pathOS),
    symPathOS(state.symPathOS),
    coveredLines(state.coveredLines),
    symbolic_arrays(state.symbolic_arrays),
    symbolic_bitvecs(state.symbolic_bitvecs),
    symbolic_ints(state.symbolic_ints),
    syt_stage(state.syt_stage),
    cexPreferences(state.cexPreferences),
    arrayNames(state.arrayNames),
    openMergeStack(state.openMergeStack),
    steppedInstructions(state.steppedInstructions),
    instsSinceCovNew(state.instsSinceCovNew),
    unwindingInformation(state.unwindingInformation
                             ? state.unwindingInformation->clone()
                             : nullptr),
    coveredNew(state.coveredNew),
    forkDisabled(state.forkDisabled),
    hasMadeSmokeTest(state.hasMadeSmokeTest),
    skipInvariantChecks(state.skipInvariantChecks),
    instHistory(state.instHistory),
    isModified(state.isModified),
    modifiedGlobals(state.modifiedGlobals),
    invDependencies(state.invDependencies),
    invNamings(state.invNamings),
    invBeingAssumed(state.invBeingAssumed) {
  for (const auto &cur_mergehandler: openMergeStack)
    cur_mergehandler->addOpenState(this);

  // deep copy the address spaces for the active invariants
  for (auto it: state.activeInvariants) {
    activeInvariants.push_back(
      InvHavocLevel {
        .ki = it.ki,
        .heap = new Heap(*it.heap),
        .addressSpace = new AddressSpace(*it.addressSpace),
        .nonHavocedModified = it.nonHavocedModified
      }
    );
  }

  // lambda constraints is a vector of vectors. Need to deep copy here.
  // Technically we should only need to deep copy the last vector, but let's be safe.
  for(unsigned i = 0; i < state.lambdaPathConstraints.size(); i++) {
    lambdaPathConstraints.push_back(std::vector<ref<Expr>>());
    for (unsigned j = 0; j < state.lambdaPathConstraints[i].size(); j++) {
      lambdaPathConstraints[i].push_back(state.lambdaPathConstraints[i][j]);
    }
  }
}

ExecutionState *ExecutionState::branch() {
  depth++;

  auto *falseState = new ExecutionState(*this);
  falseState->setID();
  falseState->coveredNew = false;
  falseState->coveredLines.clear();

  return falseState;
}

void ExecutionState::pushFrame(KInstIterator caller, KFunction *kf) {
  stack.emplace_back(StackFrame(caller, kf));
}

void ExecutionState::popFrame() {
  const StackFrame &sf = stack.back();
  for (const auto * memoryObject : sf.allocas)
    addressSpace.unbindObject(memoryObject);
  stack.pop_back();
}

void ExecutionState::addSymbolic(const MemoryObject *mo, const Array *array) {
  symbolic_arrays.emplace_back(ref<const MemoryObject>(mo), array);
}

void ExecutionState::addSymbolic(ref<BitVecExpr> bv) {
  symbolic_bitvecs.emplace_back(bv);
}

void ExecutionState::addSymbolic(ref<IntExpr> ie) {
  symbolic_ints.emplace_back(ie);
}

/**/

llvm::raw_ostream &klee::operator<<(llvm::raw_ostream &os, const MemoryMap &mm) {
  os << "{";
  MemoryMap::iterator it = mm.begin();
  MemoryMap::iterator ie = mm.end();
  if (it!=ie) {
    os << "MO" << it->first->id << ":" << it->second.get();
    for (++it; it!=ie; ++it)
      os << ", MO" << it->first->id << ":" << it->second.get();
  }
  os << "}";
  return os;
}

bool ExecutionState::merge(const ExecutionState &b) {
  assert(0 && "TPOT does not support merging for now.");
  return false;

  // if (DebugLogStateMerge)
  //   llvm::errs() << "-- attempting merge of A:" << this << " with B:" << &b
  //                << "--\n";
  // if (pc != b.pc)
  //   return false;

  // // XXX is it even possible for these to differ? does it matter? probably
  // // implies difference in object states?

  // if (symbolic_arrays != b.symbolic_arrays || symbolic_bitvecs != b.symbolic_bitvecs || symbolic_ints != b.symbolic_ints )
  //   return false;

  // {
  //   std::vector<StackFrame>::const_iterator itA = stack.begin();
  //   std::vector<StackFrame>::const_iterator itB = b.stack.begin();
  //   while (itA!=stack.end() && itB!=b.stack.end()) {
  //     // XXX vaargs?
  //     if (itA->caller!=itB->caller || itA->kf!=itB->kf)
  //       return false;
  //     ++itA;
  //     ++itB;
  //   }
  //   if (itA!=stack.end() || itB!=b.stack.end())
  //     return false;
  // }

  // std::set< ref<Expr> > aConstraints(constraints.begin(), constraints.end());
  // std::set< ref<Expr> > bConstraints(b.constraints.begin(), 
  //                                    b.constraints.end());
  // std::set< ref<Expr> > commonConstraints, aSuffix, bSuffix;
  // std::set_intersection(aConstraints.begin(), aConstraints.end(),
  //                       bConstraints.begin(), bConstraints.end(),
  //                       std::inserter(commonConstraints, commonConstraints.begin()));
  // std::set_difference(aConstraints.begin(), aConstraints.end(),
  //                     commonConstraints.begin(), commonConstraints.end(),
  //                     std::inserter(aSuffix, aSuffix.end()));
  // std::set_difference(bConstraints.begin(), bConstraints.end(),
  //                     commonConstraints.begin(), commonConstraints.end(),
  //                     std::inserter(bSuffix, bSuffix.end()));
  // if (DebugLogStateMerge) {
  //   llvm::errs() << "\tconstraint prefix: [";
  //   for (std::set<ref<Expr> >::iterator it = commonConstraints.begin(),
  //                                       ie = commonConstraints.end();
  //        it != ie; ++it)
  //     llvm::errs() << *it << ", ";
  //   llvm::errs() << "]\n";
  //   llvm::errs() << "\tA suffix: [";
  //   for (std::set<ref<Expr> >::iterator it = aSuffix.begin(),
  //                                       ie = aSuffix.end();
  //        it != ie; ++it)
  //     llvm::errs() << *it << ", ";
  //   llvm::errs() << "]\n";
  //   llvm::errs() << "\tB suffix: [";
  //   for (std::set<ref<Expr> >::iterator it = bSuffix.begin(),
  //                                       ie = bSuffix.end();
  //        it != ie; ++it)
  //     llvm::errs() << *it << ", ";
  //   llvm::errs() << "]\n";
  // }

  // // We cannot merge if addresses would resolve differently in the
  // // states. This means:
  // // 
  // // 1. Any objects created since the branch in either object must
  // // have been free'd.
  // //
  // // 2. We cannot have free'd any pre-existing object in one state
  // // and not the other

  // if (DebugLogStateMerge) {
  //   llvm::errs() << "\tchecking object states\n";
  //   llvm::errs() << "A: " << addressSpace.objects << "\n";
  //   llvm::errs() << "B: " << b.addressSpace.objects << "\n";
  // }
    
  // std::set<const MemoryObject*> mutated;
  // MemoryMap::iterator ai = addressSpace.objects.begin();
  // MemoryMap::iterator bi = b.addressSpace.objects.begin();
  // MemoryMap::iterator ae = addressSpace.objects.end();
  // MemoryMap::iterator be = b.addressSpace.objects.end();
  // for (; ai!=ae && bi!=be; ++ai, ++bi) {
  //   if (ai->first != bi->first) {
  //     if (DebugLogStateMerge) {
  //       if (ai->first < bi->first) {
  //         llvm::errs() << "\t\tB misses binding for: " << ai->first->id << "\n";
  //       } else {
  //         llvm::errs() << "\t\tA misses binding for: " << bi->first->id << "\n";
  //       }
  //     }
  //     return false;
  //   }
  //   if (ai->second.get() != bi->second.get()) {
  //     if (DebugLogStateMerge)
  //       llvm::errs() << "\t\tmutated: " << ai->first->id << "\n";
  //     mutated.insert(ai->first);
  //   }
  // }
  // if (ai!=ae || bi!=be) {
  //   if (DebugLogStateMerge)
  //     llvm::errs() << "\t\tmappings differ\n";
  //   return false;
  // }
  
  // // merge stack

  // ref<Expr> inA = ConstantExpr::alloc(1, Expr::Bool);
  // ref<Expr> inB = ConstantExpr::alloc(1, Expr::Bool);
  // for (std::set< ref<Expr> >::iterator it = aSuffix.begin(), 
  //        ie = aSuffix.end(); it != ie; ++it)
  //   inA = AndExpr::create(inA, *it);
  // for (std::set< ref<Expr> >::iterator it = bSuffix.begin(), 
  //        ie = bSuffix.end(); it != ie; ++it)
  //   inB = AndExpr::create(inB, *it);

  // // XXX should we have a preference as to which predicate to use?
  // // it seems like it can make a difference, even though logically
  // // they must contradict each other and so inA => !inB

  // std::vector<StackFrame>::iterator itA = stack.begin();
  // std::vector<StackFrame>::const_iterator itB = b.stack.begin();
  // for (; itA!=stack.end(); ++itA, ++itB) {
  //   StackFrame &af = *itA;
  //   const StackFrame &bf = *itB;
  //   for (unsigned i=0; i<af.kf->numRegisters; i++) {
  //     ref<Expr> &av = af.locals[i].value;
  //     const ref<Expr> &bv = bf.locals[i].value;
  //     if (!av || !bv) {
  //       // if one is null then by implication (we are at same pc)
  //       // we cannot reuse this local, so just ignore
  //     } else {
  //       av = SelectExpr::create(inA, av, bv);
  //     }
  //   }
  // }

  // for (std::set<const MemoryObject*>::iterator it = mutated.begin(), 
  //        ie = mutated.end(); it != ie; ++it) {
  //   const MemoryObject *mo = *it;
  //   const ObjectState *os = addressSpace.findObject(mo);
  //   const ObjectState *otherOS = b.addressSpace.findObject(mo);
  //   assert(os && !os->readOnly && 
  //          "objects mutated but not writable in merging state");
  //   assert(otherOS);

  //   ObjectState *wos = addressSpace.getWriteable(mo, os);
  //   for (unsigned i=0; i<mo->size; i++) {
  //     ref<Expr> av = wos->read8(i);
  //     ref<Expr> bv = otherOS->read8(i);
  //     wos->write(i, SelectExpr::create(inA, av, bv));
  //   }
  // }

  // constraints = ConstraintSet();

  // ConstraintManager m(constraints);
  // for (const auto &constraint : commonConstraints)
  //   m.addConstraint(constraint);
  // m.addConstraint(OrExpr::create(inA, inB));

  // return true;
}

void ExecutionState::dumpStack(llvm::raw_ostream &out) const {
  unsigned idx = 0;
  const KInstruction *target = prevPC;
  for (ExecutionState::stack_ty::const_reverse_iterator
         it = stack.rbegin(), ie = stack.rend();
       it != ie; ++it) {
    const StackFrame &sf = *it;
    Function *f = sf.kf->function;
    const InstructionInfo &ii = *target->info;
    out << "\t#" << idx++;
    std::stringstream AssStream;
    AssStream << std::setw(8) << std::setfill('0') << ii.assemblyLine;
    out << AssStream.str();
    out << " in " << f->getName().str() << " (";
    // Yawn, we could go up and print varargs if we wanted to.
    unsigned index = 0;
    for (Function::arg_iterator ai = f->arg_begin(), ae = f->arg_end();
         ai != ae; ++ai) {
      if (ai!=f->arg_begin()) out << ", ";

      out << ai->getName().str();
      // XXX should go through function
      ref<Expr> value = sf.locals[sf.kf->getArgRegister(index++)].value;
      if (isa_and_nonnull<ConstantExpr>(value))
        out << "=" << value;
    }
    out << ")";
    if (ii.file != "")
      out << " at " << ii.file << ":" << ii.line;
    out << "\n";
    target = sf.caller;
  }
}

void ExecutionState::dumpMultiResHistory() const {
  auto stream = &llvm::errs();

  // print:
  //   [all]     src location:asm line:state ID:instruction
  //   [compact]              asm line:state ID
  //   [src]     src location:asm line:state ID
  for (const auto it : multipleResHistory) {
    auto instr = it.first;
    auto resName = it.second;

    (*stream) << "     " << instr->getSourceLocation() << ':';

    (*stream) << instr->info->assemblyLine;
    (*stream) << ':' << *(instr->inst);
    (*stream) << '\n';

    (*stream) << "             " << resName << '\n';
  }
}

void ExecutionState::addConstraint(ref<Expr> e) {

  if (e->exprClass == Expr::Generic) {
    // this is a bit hacky, but for now constraints_heapOnly is unused and
    // _constraints_ stores both int and bv constraints.
    assert(constraints_heapOnly.empty());
    ConstraintManager c(constraints, constraints);
    c.addConstraint(e);
    if (!lambdaPathConstraints.empty()) {
      // add the constraint to the last lambda constraint vector
      lambdaPathConstraints.back().push_back(e);
    }
  } else if (e->exprClass == Expr::HeapLayoutOnly) {
    assert(0 && "This is unused for now");
    ConstraintManager c(constraints, constraints_heapOnly);
    c.addConstraint(e);
  } else if (e->exprClass == Expr::FZoneOnly) {
    ConstraintManager c(constraints_fZoneOnly, constraints_fZoneOnly);
    // We currently use the constraint index to idenitfy which fzone the constraint
    // belongs to, so we need to make sure that each fZone adds exactly one constraint.
    size_t prev_fzone_size = constraints_fZoneOnly.size();
    size_t prev_size = constraints.size();
    c.addConstraint(e);
    assert(constraints_fZoneOnly.size() == prev_fzone_size + 1);
    assert(constraints.size() == prev_size); // fZone constraints should not be added to the main constraint set
  } else {
    assert(false && "Invalid ExprClass");
  }
}

void ExecutionState::addCexPreference(const ref<Expr> &cond) {
  cexPreferences = cexPreferences.insert(cond);
}

ref<Expr> ExecutionState::getUnsignedConstraints(std::vector<ref<Expr>> unsignedExprs) {
  ref<Expr> res = ConstantExpr::create(1, Expr::Bool);

  for (auto &expr : unsignedExprs) {
    if (knownUnsignedExprs.find(expr) != knownUnsignedExprs.end()) {
      continue;
    }
    assert(expr->getWidth() == 0);
    res = AndExpr::create(res, 
      UleExpr::create(ConstantExpr::create(0, 64), expr));
    knownUnsignedExprs.insert(expr);
  }
  return res;
}

// for debugging purposes
unsigned int ExecutionState::curLine() const {
  KInstruction *ki = prevPC;
  return ki->info->assemblyLine;
}
