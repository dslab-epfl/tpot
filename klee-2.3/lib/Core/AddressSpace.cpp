//===-- AddressSpace.cpp --------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "AddressSpace.h"

#include "ExecutionState.h"
#include "Memory.h"
#include "TimingSolver.h"

#include "klee/Expr/Expr.h"
#include "klee/Statistics/TimerStatIncrementer.h"

#include "CoreStats.h"

#include <signal.h> // SIGINT

using namespace klee;

///

void AddressSpace::bindObject(const MemoryObject *mo, ObjectState *os) {
  assert(os->copyOnWriteOwner==0 && "object already has owner");
  os->copyOnWriteOwner = cowKey;
  objects = objects.replace(std::make_pair(mo, os));
}

void AddressSpace::unbindObject(const MemoryObject *mo) {
  objects = objects.remove(mo);
}

const ObjectState *AddressSpace::findObject(const MemoryObject *mo) const {
  const auto res = objects.lookup(mo);
  return res ? res->second.get() : nullptr;
}

ObjectState *AddressSpace::getWriteable(const MemoryObject *mo,
                                        const ObjectState *os) {
  assert(!os->readOnly);

  // If this address space owns they object, return it
  if (cowKey == os->copyOnWriteOwner)
    return const_cast<ObjectState*>(os);

  // Add a copy of this object state that can be updated
  ref<ObjectState> newObjectState(new ObjectState(*os));
  newObjectState->copyOnWriteOwner = cowKey;
  objects = objects.replace(std::make_pair(mo, newObjectState));
  return newObjectState.get();
}

/// 

bool AddressSpace::resolveOne(const ref<ConstantExpr> &addr, 
                              ObjectPair &result) const {
  uint64_t address = addr->getZExtValue();
  MemoryObject hack(address);

  if (const auto res = objects.lookup_previous(&hack)) {
    const auto &mo = res->first;
    // Check if the provided address is between start and end of the object
    // [mo->address, mo->address + mo->size) or the object is a 0-sized object.
    if ((mo->size==0 && address==mo->address) ||
        (address - mo->address < mo->size)) {
      result.first = res->first;
      result.second = res->second.get();
      return true;
    }
  }

  return false;
}

bool AddressSpace::resolveOne(ExecutionState &state,
                              TimingSolver *solver,
                              ref<Expr> address,
                              ObjectPair &result,
                              bool &success) const {
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(address)) {
    success = resolveOne(CE, result);
    return true;
  } else {
    TimerStatIncrementer timer(stats::resolveTime);

    // try cheap search, will succeed for any inbounds pointer

    //! Disable this part for now. getValue doesn't yet work properly with Z3 Integers..
    // TODO: fix this.
    // ref<ConstantExpr> cex;
    // if (!solver->getValue(state.constraints, address, cex, state.queryMetaData))
    //   return false;
    // uint64_t example = cex->getZExtValue();
    MemoryObject hack(0xFFFFFFFFFFFFFFFF);
    // const auto res = objects.lookup_previous(&hack);

    // if (res) {
    //   const MemoryObject *mo = res->first;
    //   if (example - mo->address < mo->size) {
    //     result.first = res->first;
    //     result.second = res->second.get();
    //     success = true;
    //     return true;
    //   }
    // }

    // didn't work, now we have to search
       
    MemoryMap::iterator oi = objects.upper_bound(&hack);
    MemoryMap::iterator begin = objects.begin();
    MemoryMap::iterator end = objects.end();
      
    MemoryMap::iterator start = oi;
    while (oi!=begin) {
      --oi;
      const auto &mo = oi->first;

      bool mayBeTrue;
      if (!solver->mayBeTrue(state.constraints,
                             mo->getBoundsCheckPointer(address), mayBeTrue,
                             state.queryMetaData))
        return false;
      if (mayBeTrue) {
        result.first = oi->first;
        result.second = oi->second.get();
        success = true;
        return true;
      } else {
        bool mustBeTrue;
        if (!solver->mustBeTrue(state.constraints,
                                UgeExpr::create(address, mo->getBaseExpr()),
                                mustBeTrue, state.queryMetaData))
          return false;
        if (mustBeTrue)
          break;
      }
    }

    // search forwards
    for (oi=start; oi!=end; ++oi) {
      const auto &mo = oi->first;

      bool mustBeTrue;
      if (!solver->mustBeTrue(state.constraints,
                              UltExpr::create(address, mo->getBaseExpr()),
                              mustBeTrue, state.queryMetaData))
        return false;
      if (mustBeTrue) {
        break;
      } else {
        bool mayBeTrue;

        if (!solver->mayBeTrue(state.constraints,
                               mo->getBoundsCheckPointer(address), mayBeTrue,
                               state.queryMetaData))
          return false;
        if (mayBeTrue) {
          result.first = oi->first;
          result.second = oi->second.get();
          success = true;
          return true;
        }
      }
    }

    success = false;
    return true;
  }
}

int AddressSpace::checkPointerInObject(ExecutionState &state,
                                       TimingSolver *solver, ref<Expr> p,
                                       const ObjectPair &op, ResolutionList &rl,
                                       unsigned maxResolutions) const {
  // XXX in the common case we can save one query if we ask
  // mustBeTrue before mayBeTrue for the first result. easy
  // to add I just want to have a nice symbolic test case first.
  const MemoryObject *mo = op.first;
  ref<Expr> inBounds = mo->getBoundsCheckPointer(p);
  bool mayBeTrue;
  if (!solver->mayBeTrue(state.constraints, inBounds, mayBeTrue,
                         state.queryMetaData)) {
    return 1;
  }

  if (mayBeTrue) {
    rl.push_back(op);

    // fast path check
    auto size = rl.size();
    if (size == 1) {
      bool mustBeTrue;
      if (!solver->mustBeTrue(state.constraints, inBounds, mustBeTrue,
                              state.queryMetaData))
        return 1;
      if (mustBeTrue)
        return 0;
    }
    else
      if (size == maxResolutions)
        return 1;
  }

  return 2;
}

bool AddressSpace::resolve(ExecutionState &state, TimingSolver *solver,
                           ref<Expr> p, ResolutionList &rl,
                           unsigned maxResolutions, time::Span timeout, 
                           ref<Expr> extraConstraint) const {
  assert(extraConstraint.isNull() && "extraConstraint not supported for non-heap resolution yet");

  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(p)) {
    ObjectPair res;
    if (resolveOne(CE, res))
      rl.push_back(res);
    return false;
  } else {
    TimerStatIncrementer timer(stats::resolveTime);

    // XXX in general this isn't exactly what we want... for
    // a multiple resolution case (or for example, a \in {b,c,0})
    // we want to find the first object, find a cex assuming
    // not the first, find a cex assuming not the second...
    // etc.

    // XXX how do we smartly amortize the cost of checking to
    // see if we need to keep searching up/down, in bad cases?
    // maybe we don't care?

    // XXX we really just need a smart place to start (although
    // if its a known solution then the code below is guaranteed
    // to hit the fast path with exactly 2 queries). we could also
    // just get this by inspection of the expr.

    ref<ConstantExpr> cex;
    if (!solver->getValue(state.constraints, p, cex, state.queryMetaData))
      return true;
    uint64_t example = cex->getZExtValue();
    MemoryObject hack(example);

    MemoryMap::iterator oi = objects.upper_bound(&hack);
    MemoryMap::iterator begin = objects.begin();
    MemoryMap::iterator end = objects.end();

    MemoryMap::iterator start = oi;
    // search backwards, start with one minus because this
    // is the object that p *should* be within, which means we
    // get write off the end with 4 queries
    while (oi != begin) {
      --oi;
      const MemoryObject *mo = oi->first;
      if (timeout && timeout < timer.delta())
        return true;

      auto op = std::make_pair<>(mo, oi->second.get());

      int incomplete =
          checkPointerInObject(state, solver, p, op, rl, maxResolutions);
      if (incomplete != 2)
        return incomplete ? true : false;

      bool mustBeTrue;
      if (!solver->mustBeTrue(state.constraints,
                              UgeExpr::create(p, mo->getBaseExpr()), mustBeTrue,
                              state.queryMetaData))
        return true;
      if (mustBeTrue)
        break;
    }

    // search forwards
    for (oi = start; oi != end; ++oi) {
      const MemoryObject *mo = oi->first;
      if (timeout && timeout < timer.delta())
        return true;

      bool mustBeTrue;
      if (!solver->mustBeTrue(state.constraints,
                              UltExpr::create(p, mo->getBaseExpr()), mustBeTrue,
                              state.queryMetaData))
        return true;
      if (mustBeTrue)
        break;
      auto op = std::make_pair<>(mo, oi->second.get());

      int incomplete =
          checkPointerInObject(state, solver, p, op, rl, maxResolutions);
      if (incomplete != 2)
        return incomplete ? true : false;
    }
  }

  return false;
}

// These two are pretty big hack so we can sort of pass memory back
// and forth to externals. They work by abusing the concrete cache
// store inside of the object states, which allows them to
// transparently avoid screwing up symbolics (if the byte is symbolic
// then its concrete cache byte isn't being used) but is just a hack.

void AddressSpace::copyOutConcretes() {
  for (MemoryMap::iterator it = objects.begin(), ie = objects.end(); 
       it != ie; ++it) {
    const MemoryObject *mo = it->first;

    if (!mo->isUserSpecified) {
      const auto &os = it->second;
      auto address = reinterpret_cast<std::uint8_t*>(mo->address);

      if (!os->readOnly)
        memcpy(address, os->concreteStore, mo->size);
    }
  }
}

bool AddressSpace::copyInConcretes() {
  for (auto &obj : objects) {
    const MemoryObject *mo = obj.first;

    if (!mo->isUserSpecified) {
      const auto &os = obj.second;

      if (!copyInConcrete(mo, os.get(), mo->address))
        return false;
    }
  }

  return true;
}

bool AddressSpace::copyInConcrete(const MemoryObject *mo, const ObjectState *os,
                                  uint64_t src_address) {
  auto address = reinterpret_cast<std::uint8_t*>(src_address);
  if (memcmp(address, os->concreteStore, mo->size) != 0) {
    if (os->readOnly) {
      return false;
    } else {
      ObjectState *wos = getWriteable(mo, os);
      memcpy(wos->concreteStore, address, mo->size);
    }
  }
  return true;
}

/***/

bool MemoryObjectLT::operator()(const MemoryObject *a, const MemoryObject *b) const {
  return a->address < b->address;
}

/*
    Heap
*/

const ObjectState *Heap::findObject(const MemoryObject *mo) const {
  for (auto &op : heapObjects) {
    if (op.first == mo)
      return op.second;
  }
  return NULL;
}

void Heap::bindObject(const MemoryObject *mo, ObjectState *os) {
  assert(mo->address == 0 && !mo->uniqueHeapAddress.isNull() &&
        "binding memory object with concrete address in heap");
  assert(!findObject(mo));
  heapObjects.push_back(std::make_pair(mo, os));
}

bool Heap::resolveOne(const ref<ConstantExpr> &address, ObjectPair &result) const {
  if (heapObjects.empty())
    return false;
  // This should never be called otherwise.
  assert(0);
}

bool Heap::resolveOne(ExecutionState &state, 
                TimingSolver *solver,
                ref<Expr> address,
                ObjectPair &result,
                bool &success) const {
  //? Isn't the success output param redundant?

  // Check the cache.
  // auto rc_it = resolutionCache.find(address);
  // if ( rc_it != resolutionCache.end() ) {
  //   int idx = rc_it->second;
  //   assert(idx >= 0 && idx < heapObjects.size());
  //   result = heapObjects[idx];
  //   success = true;
  //   return true;
  // }

  // Check hints
  // auto rs_it = resolutionHints.find(address);
  // if ( rs_it == resolutionHints.end() ) {
  //   // retry the resolution hints if this is a struct field ptr.
  //   if (const AddExpr *OE = dyn_cast<AddExpr>(address)) {
  //     rs_it = resolutionHints.find(OE->left);
  //     if ( rs_it == resolutionHints.end() )
  //       rs_it = resolutionHints.find(OE->right);
  //   }
  // }

  // if ( rs_it != resolutionHints.end() ) {
  //   int idx = rc_it->second;
    
  //   if(!(idx >= 0 && idx < heapObjects.size())) raise(SIGINT);

  //   // TODO: put this bit in a helper function

  //   ObjectPair &it = heapObjects[idx];
  //   const MemoryObject *mo = it.first;
  //   assert(mo->address == 0 && !mo->uniqueHeapAddress.isNull() &&
  //         "heap has a memory object with concrete address");

  //   ref<Expr> relative_address = SubExpr::create(address, mo->uniqueHeapAddress);
  //   // temporary hack. Pretend this is a 0-byte access to implement resolveOne's semantics
  //   ref<Expr> offset = mo->getOffsetExpr(relative_address);
  //   ref<Expr> check = mo->getBoundsCheckOffset(offset, 1);
  //   // check = optimizer.optimizeExpr(check, true);

  //   SYT_PRINT_STEPS("resolveOne -> calling mayBeTrue");
  //   bool found = false;
  //   bool solver_success = solver->mayBeTrue(state.constraints, check, found,
  //                                     state.queryMetaData);
  //   assert(solver_success);
  //   if (found) {
  //     SYT_PRINT_STEPS(" ---  resolution hint HIT  ---");
  //     result = it;
  //     success = true;
  //     resolutionCache[address] = idx;
  //     return true;
  //   }
  //   SYT_PRINT_STEPS(" ---  resolution hint MISS  ---");
  // }

  bool found = false;
  // Reverse iteration is better here. We usually deref a pointer
  // after declaring it to be unique.
  for (int i = heapObjects.size() - 1;
    !success && i >= 0; i--) {
    ObjectPair &it = heapObjects[i];
    const MemoryObject *mo = it.first;
    assert(mo->address == 0 && !mo->uniqueHeapAddress.isNull() &&
          "heap has a memory object with concrete address");

    ref<Expr> relative_address = SubExpr::create(address, mo->uniqueHeapAddress);
    // temporary hack. Pretend this is a 1-byte access to implement resolveOne's semantics
    ref<Expr> offset = mo->getOffsetExpr(relative_address);
    ref<Expr> check = mo->getBoundsCheckOffset(offset, 1);
    // check = optimizer.optimizeExpr(check, true);

    LOG_MEMORY_RESOLUTION("resolveOne -> calling mayBeTrue");
    bool solver_success = solver->mayBeTrue(state.constraints, check, found,
                                      state.queryMetaData);
    assert(solver_success);
    if (found) {
      result = it;
      success = true;
      resolutionCache[address] = i;
      return true;
    }
  }
  success = false;
  return false;
}

bool Heap::resolve(ExecutionState &state,
              TimingSolver *solver,
              ref<Expr> p,
              ResolutionList &rl, 
              unsigned maxResolutions,
              time::Span timeout,
              ref<Expr> extraConstraint) const {
  for (auto it = heapObjects.begin();
       it != heapObjects.end(); it++) {
    const MemoryObject *mo = it->first;
    
    if (mayResolveTo(state, solver, mo, p, extraConstraint)) {
      rl.push_back(*it);
    }
  }
  return false;
}

ObjectState *Heap::getWriteable(const MemoryObject *mo, const ObjectState *os) {
  // // For now, we don't do CoW, so we just return the object state.
  // return const_cast<ObjectState *>(os);

  // return the copy of OS that mo is bound to in this address space
  return const_cast<ObjectState *>(findObject(mo));
};

bool Heap::mayResolveTo(ExecutionState &state,  TimingSolver *solver, 
                        const MemoryObject *mo, ref<Expr> address, ref<Expr> extraConstraint) {
  assert(mo->address == 0 && !mo->uniqueHeapAddress.isNull() &&
          "heap has a memory object with concrete address");
  
  ref<Expr> relative_address = SubExpr::create(address, mo->uniqueHeapAddress);
  // temporary hack. Pretend this is a 1-byte access to implement resolveOne's semantics
  ref<Expr> offset = mo->getOffsetExpr(relative_address);
  ref<Expr> check = mo->getBoundsCheckOffset(offset, 1);
  //check = optimizer.optimizeExpr(check, true);
  
  ConstraintSet c = state.constraints;
  if (!extraConstraint.isNull()) {
    std::vector<ref<Expr>> singletonVector = {extraConstraint};
    ConstraintSet singleton(singletonVector);

    c = c.join(singleton);
    c.readSimplCache = state.getConstraints(true).readSimplCache;
    c.readSimplKnownFailures = state.getConstraints(true).readSimplKnownFailures;
    c.addressSimplTable = state.getConstraints(true).addressSimplTable;
  } 
  
  bool success;
  bool solver_success = solver->mayBeTrue(c, check, success,
                                    state.queryMetaData);
  assert(solver_success);
  return success;
}