//===-- Memory.cpp --------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "Memory.h"

#include "Context.h"
#include "ExecutionState.h"
#include "MemoryManager.h"

#include "klee/ADT/BitArray.h"
#include "klee/Expr/ArrayCache.h"
#include "klee/Expr/Constraints.h"
#include "klee/Expr/Expr.h"
#include "klee/Support/OptionCategories.h"
#include "klee/Solver/Solver.h"
#include "klee/Support/ErrorHandling.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include <cassert>
#include <sstream>
#include <ctime>
#include <unistd.h>

using namespace llvm;
using namespace klee;

namespace {
  cl::opt<bool>
  UseConstantArrays("use-constant-arrays",
                    cl::desc("Use constant arrays instead of updates when possible (default=true)\n"),
                    cl::init(true),
                    cl::cat(SolvingCat));
}

static bool isHeapObject(ref<const MemoryObject> mo) {
  return mo->address == 0 && !mo->uniqueHeapAddress.isNull();
}

/***/

int MemoryObject::counter = 0;

MemoryObject::~MemoryObject() {
  if (parent)
    parent->markFreed(this);
}

void MemoryObject::getAllocInfo(std::string &result) const {
  llvm::raw_string_ostream info(result);

  info << "MO" << id << "[" << size << "]";

  if (allocSite) {
    info << " allocated at ";
    if (const Instruction *i = dyn_cast<Instruction>(allocSite)) {
      info << i->getParent()->getParent()->getName() << "():";
      info << *i;
    } else if (const GlobalValue *gv = dyn_cast<GlobalValue>(allocSite)) {
      info << "global:" << gv->getName();
    } else {
      info << "value:" << *allocSite;
    }
  } else {
    info << " (no allocation info)";
  }
  
  info.flush();
}

/***/

ObjectState::ObjectState(const MemoryObject *mo)
  : copyOnWriteOwner(0),
    object(mo),
    concreteStore(new uint8_t[mo->size]),
    concreteMask(nullptr),
    knownSymbolics(nullptr),
    unflushedMask(nullptr),
    updates(nullptr, nullptr),
    size(mo->size),
    readOnly(false) {
  if (!UseConstantArrays) {
    static unsigned id = 0;
    const Array *array =
        getArrayCache()->CreateArray("tmp_arr" + llvm::utostr(++id), size);
    updates = UpdateList(array, 0);
  }
  memset(concreteStore, 0, size);
}


ObjectState::ObjectState(const MemoryObject *mo, const Array *array, bool useBVRepr)
  : copyOnWriteOwner(0),
    object(mo),
    concreteStore(new uint8_t[mo->size]),
    concreteMask(nullptr),
    knownSymbolics(nullptr),
    unflushedMask(nullptr),
    updates(array, nullptr),
    size(mo->size),
    readOnly(false) {
  makeSymbolic();
  memset(concreteStore, 0, size);

  // let's just use BV representations for small objects now
  if (useBVRepr && (mo->size == 1 || mo->size == 4 || mo->size == 8)) {
    bitVecRepresentation = BitVecExpr::create(mo->name + "_init_bitvec", mo->size * 8);
    old_bitVecRepresentation = bitVecRepresentation;
    isBitVec = true;
  } else {
    isBitVec = false;
  }
}

ObjectState::ObjectState(const ObjectState &os) 
  : copyOnWriteOwner(0),
    object(os.object),
    concreteStore(new uint8_t[os.size]),
    concreteMask(os.concreteMask ? new BitArray(*os.concreteMask, os.size) : nullptr),
    knownSymbolics(nullptr),
    unflushedMask(os.unflushedMask ? new BitArray(*os.unflushedMask, os.size) : nullptr),
    updates(os.updates),
    size(os.size),
    isBitVec(os.isBitVec),
    bitVecRepresentation(os.bitVecRepresentation),
    old_bitVecRepresentation(os.old_bitVecRepresentation),
    readOnly(false) {
  assert(!os.readOnly && "no need to copy read only object?");
  if (os.knownSymbolics) {
    knownSymbolics = new ref<Expr>[size];
    for (unsigned i=0; i<size; i++)
      knownSymbolics[i] = os.knownSymbolics[i];
  }

  memcpy(concreteStore, os.concreteStore, size*sizeof(*concreteStore));
}

ObjectState::~ObjectState() {
  delete concreteMask;
  delete unflushedMask;
  delete[] knownSymbolics;
  delete[] concreteStore;
}

ArrayCache *ObjectState::getArrayCache() const {
  assert(object && "object was NULL");
  return object->parent->getArrayCache();
}

/***/

const UpdateList &ObjectState::getUpdates(bool ignoreWrites) const {
  // Constant arrays are created lazily.
  if (!updates.root) {
    assert(0 && "Unexpected behavior in TPOT. Turn off use-constant-arrays?");
    // Collect the list of writes, with the oldest writes first.
    
    // FIXME: We should be able to do this more efficiently, we just need to be
    // careful to get the interaction with the cache right. In particular we
    // should avoid creating UpdateNode instances we never use.
    unsigned NumWrites = updates.head ? updates.head->getSize() : 0;
    std::vector< std::pair< ref<Expr>, ref<Expr> > > Writes(NumWrites);
    const auto *un = updates.head.get();
    for (unsigned i = NumWrites; i != 0; un = un->next.get()) {
      --i;
      Writes[i] = std::make_pair(un->index, un->value);
    }

    std::vector< ref<ConstantExpr> > Contents(size);

    // Initialize to zeros.
    for (unsigned i = 0, e = size; i != e; ++i)
      Contents[i] = ConstantExpr::create(0, Expr::Int8);

    // Pull off as many concrete writes as we can.
    unsigned Begin = 0, End = Writes.size();
    for (; Begin != End; ++Begin) {
      // Push concrete writes into the constant array.
      ConstantExpr *Index = dyn_cast<ConstantExpr>(Writes[Begin].first);
      if (!Index)
        break;

      ConstantExpr *Value = dyn_cast<ConstantExpr>(Writes[Begin].second);
      if (!Value)
        break;

      Contents[Index->getZExtValue()] = Value;
    }

    static unsigned id = 0;
    const Array *array = getArrayCache()->CreateArray(
        "const_arr" + llvm::utostr(++id), size, &Contents[0],
        &Contents[0] + Contents.size());
    updates = UpdateList(array, 0);

    // Apply the remaining (non-constant) writes.
    for (; Begin != End; ++Begin)
      updates.extend(Writes[Begin].first, Writes[Begin].second);
  }

  if (!ignoreWrites) {
    return updates;
  } 
  return *(new UpdateList(updates.root, nullptr));
}

void ObjectState::flushToConcreteStore(TimingSolver *solver,
                                       const ExecutionState &state) const {
  for (unsigned i = 0; i < size; i++) {
    if (isByteKnownSymbolic(i)) {
      ref<ConstantExpr> ce;
      bool success = solver->getValue(state.constraints, read8(i, false), ce,
                                      state.queryMetaData);
      if (!success)
        klee_warning("Solver timed out when getting a value for external call, "
                     "byte %p+%u will have random value",
                     (void *)object->address, i);
      else
        ce->toMemory(concreteStore + i);
    }
  }
}

bool ObjectState::forceFlushToConcreteStore(TimingSolver *solver,
                                            ExecutionState &state) const {
  for (unsigned i = 0; i < size; i++) {
    ref<ConstantExpr> ce;
    bool success = solver->getValue(state.constraints, read8(i, false), ce,
                                    state.queryMetaData);
    if (!success) {
      klee_warning("Solver timed out when getting a value for external call, "
                    "byte %p+%u will have random value",
                    (void *)object->address, i);
      return false;
    }
    // else {
    //   if (moreRandom) {
    //       ref<ConstantExpr> tmp;
    //       // TODO: this is not scalable and efficient, but it is a quick fix
    //       ConstraintSet c(state.constraints);
    //       srandom(std::time(0) ^ getpid());
    //       int r = random() % 5;
    //       for (int j = 0; j < r; j++) {
    //         ref<Expr> x = read8(i);
    //         ref<Expr> zero = ConstantExpr::create(ce->getAPValue().getZExtValue(), Expr::Int8);
    //         ref<Expr> ne = NeExpr::create(x, zero);
    //         c.push_back(ne);
          
    //         bool success = solver->getValue(c, read8(i), tmp,
    //                                   state.queryMetaData);
    //         if (!success) {
    //           klee_warning("Solver timed out when getting a value for external call, "
    //                       "byte %p+%u will have random value",
    //                       (void *)object->address, i);
    //           break;
    //         }
    //         ce = tmp;
    //       }
    //       srandom(1);
    //   }
    // }
    ce->toMemory(concreteStore + i);
  }
  return true;
}

uint8_t ObjectState::getConcrete(unsigned offset) const {
  return concreteStore[offset];
}

void ObjectState::makeConcrete() {
  delete concreteMask;
  delete unflushedMask;
  delete[] knownSymbolics;
  concreteMask = nullptr;
  unflushedMask = nullptr;
  knownSymbolics = nullptr;
}

void ObjectState::makeSymbolic() {
  assert(!updates.head &&
         "XXX makeSymbolic of objects with symbolic values is unsupported");

  // XXX simplify this, can just delete various arrays I guess
  for (unsigned i=0; i<size; i++) {
    markByteSymbolic(i);
    setKnownSymbolic(i, 0);
    markByteFlushed(i);
  }
}

void ObjectState::initializeToZero() {
  makeConcrete();
  memset(concreteStore, 0, size);
}

void ObjectState::initializeToRandom() {  
  makeConcrete();
  for (unsigned i=0; i<size; i++) {
    // randomly selected by 256 sided die
    concreteStore[i] = 0xAB;
  }
}

/*
Cache Invariants
--
isByteKnownSymbolic(i) => !isByteConcrete(i)
isByteConcrete(i) => !isByteKnownSymbolic(i)
isByteUnflushed(i) => (isByteConcrete(i) || isByteKnownSymbolic(i))
 */

void ObjectState::fastRangeCheckOffset(ref<Expr> offset,
                                       unsigned *base_r,
                                       unsigned *size_r) const {
  *base_r = 0;
  *size_r = size;
}

void ObjectState::flushRangeForRead(unsigned rangeBase,
                                    unsigned rangeSize) const {
  if (!unflushedMask)
    unflushedMask = new BitArray(size, true);

  for (unsigned offset = rangeBase; offset < rangeBase + rangeSize; offset++) {
    if (isByteUnflushed(offset)) {
      if (isByteConcrete(offset)) {
        updates.extend(ConstantExpr::create(offset, Expr::Int32),
                       ConstantExpr::create(concreteStore[offset], Expr::Int8));
      } else {
        assert(isByteKnownSymbolic(offset) &&
               "invalid bit set in unflushedMask");
        updates.extend(ConstantExpr::create(offset, Expr::Int32),
                       knownSymbolics[offset]);
      }

      unflushedMask->unset(offset);
    }
  }
}

void ObjectState::flushRangeForWrite(unsigned rangeBase, unsigned rangeSize) {
  if (!unflushedMask)
    unflushedMask = new BitArray(size, true);

  for (unsigned offset = rangeBase; offset < rangeBase + rangeSize; offset++) {
    if (isByteUnflushed(offset)) {
      if (isByteConcrete(offset)) {
        updates.extend(ConstantExpr::create(offset, Expr::Int32),
                       ConstantExpr::create(concreteStore[offset], Expr::Int8));
        markByteSymbolic(offset);
      } else {
        assert(isByteKnownSymbolic(offset) &&
               "invalid bit set in unflushedMask");
        updates.extend(ConstantExpr::create(offset, Expr::Int32),
                       knownSymbolics[offset]);
        setKnownSymbolic(offset, 0);
      }

      unflushedMask->unset(offset);
    } else {
      // flushed bytes that are written over still need
      // to be marked out
      if (isByteConcrete(offset)) {
        markByteSymbolic(offset);
      } else if (isByteKnownSymbolic(offset)) {
        setKnownSymbolic(offset, 0);
      }
    }
  }
}

bool ObjectState::isByteConcrete(unsigned offset) const {
  return !concreteMask || concreteMask->get(offset);
}

bool ObjectState::isByteUnflushed(unsigned offset) const {
  return !unflushedMask || unflushedMask->get(offset);
}

bool ObjectState::isByteKnownSymbolic(unsigned offset) const {
  return knownSymbolics && knownSymbolics[offset].get();
}

void ObjectState::markByteConcrete(unsigned offset) {
  if (concreteMask)
    concreteMask->set(offset);
}

void ObjectState::markByteSymbolic(unsigned offset) {
  if (!concreteMask)
    concreteMask = new BitArray(size, true);
  concreteMask->unset(offset);
}

void ObjectState::markByteUnflushed(unsigned offset) {
  if (unflushedMask)
    unflushedMask->set(offset);
}

void ObjectState::markByteFlushed(unsigned offset) {
  if (!unflushedMask) {
    unflushedMask = new BitArray(size, false);
  } else {
    unflushedMask->unset(offset);
  }
}

void ObjectState::setKnownSymbolic(unsigned offset, 
                                   Expr *value /* can be null */) {
  if (knownSymbolics) {
    knownSymbolics[offset] = value;
  } else {
    if (value) {
      knownSymbolics = new ref<Expr>[size];
      knownSymbolics[offset] = value;
    }
  }
}

/***/

ref<Expr> ObjectState::read8(unsigned offset, bool ignoreWrites) const {
  if (isByteConcrete(offset)) {
    assert(!ignoreWrites && "concrete byte with ignoreWrites");
    return ConstantExpr::create(concreteStore[offset], Expr::Int8);
  } else if (isByteKnownSymbolic(offset)) {
    assert(!ignoreWrites && "known symbolic byte with ignoreWrites");
    return knownSymbolics[offset];
  } else {
    assert(!isByteUnflushed(offset) && "unflushed byte without cache value");
    
    return ReadExpr::create(getUpdates(ignoreWrites), 
                            ConstantExpr::create(offset, Expr::Int32));
  }    
}

ref<Expr> ObjectState::read8(ref<Expr> offset, bool ignoreWrites) const {
  assert(!isa<ConstantExpr>(offset) && "constant offset passed to symbolic read8");
  unsigned base, size;
  fastRangeCheckOffset(offset, &base, &size);
  flushRangeForRead(base, size);

  if (size>4096) {
    std::string allocInfo;
    object->getAllocInfo(allocInfo);
    klee_warning_once(0, "flushing %d bytes on read, may be slow and/or crash: %s", 
                      size,
                      allocInfo.c_str());
  }
  offset = adjustOffsetWidth(offset);
  return ReadExpr::create(getUpdates(ignoreWrites), offset);
}

void ObjectState::write8(unsigned offset, uint8_t value) {
  //assert(read_only == false && "writing to read-only object!");
  concreteStore[offset] = value;
  setKnownSymbolic(offset, 0);

  markByteConcrete(offset);
  markByteUnflushed(offset);
}

void ObjectState::write8(unsigned offset, ref<Expr> value) {
  // can happen when ExtractExpr special cases
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(value)) {
    write8(offset, (uint8_t) CE->getZExtValue(8));
  } else {
    setKnownSymbolic(offset, value.get());
      
    markByteSymbolic(offset);
    markByteUnflushed(offset);
  }
}

void ObjectState::write8(ref<Expr> offset, ref<Expr> value) {
  assert(!isa<ConstantExpr>(offset) && "constant offset passed to symbolic write8");
  unsigned base, size;
  fastRangeCheckOffset(offset, &base, &size);
  flushRangeForWrite(base, size);

  if (size>4096) {
    std::string allocInfo;
    object->getAllocInfo(allocInfo);
    klee_warning_once(0, "flushing %d bytes on read, may be slow and/or crash: %s", 
                      size,
                      allocInfo.c_str());
  }
  
  updates.extend(adjustOffsetWidth(offset), value);
}

/***/

ref<Expr> ObjectState::adjustOffsetWidth(ref<Expr> offset) const {
  if (isHeapObject(object)) {
    // this is a heap object, and so it it indexed by a Z3 integer, not a bitvector
    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(offset)) {
      ref<ConstantExpr> ret = ConstantExpr::alloc(CE->value);
      ret->producesInt = true;
      return ret;
    }
    assert(offset->getWidth() == 0);
    return offset;
  } else {
    // Truncate offset to 32-bits.
    return ZExtExpr::create(offset, Expr::Int32);
  }
}


ref<Expr> ObjectState::read(ref<Expr> offset, Expr::Width width, bool ignoreWrites) const {
  offset = adjustOffsetWidth(offset);

  // Check for reads at constant offsets.
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(offset))
    return read(CE->getZExtValue(32), width, ignoreWrites);

  assert(!isBitVec && "bitvec read not supported at a symbolic offset");

  // Treat bool specially, it is the only non-byte sized write we allow.
  if (width == Expr::Bool)
    return ExtractExpr::create(read8(offset, ignoreWrites), 0, Expr::Bool);

  // Otherwise, follow the slow general case.
  unsigned NumBytes = width / 8;
  assert(width == NumBytes * 8 && "Invalid read size!");
  ref<Expr> Res(0);
  for (unsigned i = 0; i != NumBytes; ++i) {
    unsigned idx = Context::get().isLittleEndian() ? i : (NumBytes - i - 1);
    ref<Expr> Byte = read8(AddExpr::create(offset, 
                                           ConstantExpr::create(idx, 
                                                                Expr::Int32)), ignoreWrites);
    Res = i ? ConcatExpr::create(Byte, Res) : Byte;
  }

  return Res;
}

ref<Expr> ObjectState::read(unsigned offset, Expr::Width width, bool ignoreWrites) const {
  if (isBitVec) {
    assert(width == size * 8 && "bitvec read size must match object size");
    return ignoreWrites ? old_bitVecRepresentation : bitVecRepresentation;
  }

  // Treat bool specially, it is the only non-byte sized write we allow.
  if (width == Expr::Bool)
    return ExtractExpr::create(read8(offset, ignoreWrites), 0, Expr::Bool);

  // Otherwise, follow the slow general case.
  unsigned NumBytes = width / 8;
  assert(width == NumBytes * 8 && "Invalid width for read size!");
  ref<Expr> Res(0);
  for (unsigned i = 0; i != NumBytes; ++i) {
    unsigned idx = Context::get().isLittleEndian() ? i : (NumBytes - i - 1);
    ref<Expr> Byte = read8(offset + idx, ignoreWrites);
    Res = i ? ConcatExpr::create(Byte, Res) : Byte;
  }

  return Res;
}

void ObjectState::write(ref<Expr> offset, ref<Expr> value) {
  // Truncate offset to 32-bits.
  offset = adjustOffsetWidth(offset);

  // Check for writes at constant offsets.
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(offset)) {
    write(CE->getZExtValue(32), value);
    return;
  }

  assert(!isBitVec && "bitvec write not supported at a symbolic offset");

  // Treat bool specially, it is the only non-byte sized write we allow.
  Expr::Width w = value->getWidth();
  if (w == Expr::Bool) {
    write8(offset, ZExtExpr::create(value, Expr::Int8));
    return;
  }

  // Otherwise, follow the slow general case.
  unsigned NumBytes = w / 8;
  assert(w == NumBytes * 8 && "Invalid write size!");
  for (unsigned i = 0; i != NumBytes; ++i) {
    unsigned idx = Context::get().isLittleEndian() ? i : (NumBytes - i - 1);
    write8(AddExpr::create(offset, ConstantExpr::create(idx, Expr::Int32)),
           ExtractExpr::create(value, 8 * i, Expr::Int8));
  }
}

void ObjectState::write(unsigned offset, ref<Expr> value) {

  if (isBitVec) {
    assert(offset == 0 && value->getWidth() == size * 8 && "bitvec write size must match object size");
    assert(!bitVecRepresentation.isNull() && !old_bitVecRepresentation.isNull());
    bitVecRepresentation = value;
    return;
  }

  // Check for writes of constant values.
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(value)) {
    Expr::Width w = CE->getWidth();
    if (w <= 64 && klee::bits64::isPowerOfTwo(w)) {
      uint64_t val = CE->getZExtValue();
      switch (w) {
      default: assert(0 && "Invalid write size!");
      case  Expr::Bool:
      case  Expr::Int8:  write8(offset, val); return;
      case Expr::Int16: write16(offset, val); return;
      case Expr::Int32: write32(offset, val); return;
      case Expr::Int64: write64(offset, val); return;
      }
    }
  }

  // Treat bool specially, it is the only non-byte sized write we allow.
  Expr::Width w = value->getWidth();
  if (w == Expr::Bool) {
    write8(offset, ZExtExpr::create(value, Expr::Int8));
    return;
  }

  // Otherwise, follow the slow general case.
  unsigned NumBytes = w / 8;
  assert(w == NumBytes * 8 && "Invalid write size!");
  for (unsigned i = 0; i != NumBytes; ++i) {
    unsigned idx = Context::get().isLittleEndian() ? i : (NumBytes - i - 1);
    write8(offset + idx, ExtractExpr::create(value, 8 * i, Expr::Int8));
  }
} 

void ObjectState::write16(unsigned offset, uint16_t value) {
  unsigned NumBytes = 2;
  for (unsigned i = 0; i != NumBytes; ++i) {
    unsigned idx = Context::get().isLittleEndian() ? i : (NumBytes - i - 1);
    write8(offset + idx, (uint8_t) (value >> (8 * i)));
  }
}

void ObjectState::write32(unsigned offset, uint32_t value) {
  unsigned NumBytes = 4;
  for (unsigned i = 0; i != NumBytes; ++i) {
    unsigned idx = Context::get().isLittleEndian() ? i : (NumBytes - i - 1);
    write8(offset + idx, (uint8_t) (value >> (8 * i)));
  }
}

void ObjectState::write64(unsigned offset, uint64_t value) {
  unsigned NumBytes = 8;
  for (unsigned i = 0; i != NumBytes; ++i) {
    unsigned idx = Context::get().isLittleEndian() ? i : (NumBytes - i - 1);
    write8(offset + idx, (uint8_t) (value >> (8 * i)));
  }
}

void ObjectState::print() const {
  llvm::errs() << "-- ObjectState --\n";
  llvm::errs() << "\tMemoryObject ID: " << object->id << "\n";
  llvm::errs() << "\tRoot Object: " << updates.root << "\n";
  llvm::errs() << "\tSize: " << size << "\n";

  llvm::errs() << "\tBytes:\n";
  for (unsigned i=0; i<size; i++) {
    llvm::errs() << "\t\t["<<i<<"]"
               << " concrete? " << isByteConcrete(i)
               << " known-sym? " << isByteKnownSymbolic(i)
               << " unflushed? " << isByteUnflushed(i) << " = ";
    ref<Expr> e = read8(i, false);
    llvm::errs() << e << "\n";
  }

  llvm::errs() << "\tUpdates:\n";
  for (const auto *un = updates.head.get(); un; un = un->next.get()) {
    llvm::errs() << "\t\t[" << un->index << "] = " << un->value << "\n";
  }
}

bool ObjectState::name(std::string n) {
  const SytSSObjectState *sos = dynamic_cast<const SytSSObjectState *>(this);
  if (sos && sos->isFreed) {
    return false;
  }
  if (syt_name == n)
    return true;
  if (syt_name == "") {
    syt_name = n;
    return true;
  } 
  return false;
}

// // Is the object provably unmodified between [offset, offset + width)?
// bool ObjectState::unmodifiedAt(TimingSolver *solver, const ExecutionState &state,
//                                ref<Expr> offset, Expr::Width width) const {
//   // Assumption: the root of the underlying array is the object at initial state.
//   if (!updates.root) {
//     assert(0 && "TPOT does not account for lazy intialization");
//   }
  
//   ref<UpdateNode> cur = updates.head;
//   while (cur) {
//     // check if the update may overlap with [offset, offset + width)
//     ref<Expr> noOverlap = OrExpr::create(
//       UleExpr::create(
//         AddExpr::create(offset, ConstantExpr::create(width, Expr::Int32)),
//         cur->index),
//       UleExpr::create(
//         AddExpr::create(cur->index, ConstantExpr::create(cur->getSize(), Expr::Int32)),
//         offset));
    
//     bool res;
//     bool solver_success = solver->mustBeTrue(
//       state.getConstraints(/*useHeapConstraints=*/true), noOverlap, res, state.queryMetaData);
//     assert(solver_success && "FIXME: Unhandled solver failure");
//     if (!res) {
//       // There may be an overlap
//       return false;
//     }

//     cur = cur->next;
//   }
//   return true;
// }

// Is the object provably unmodified between [offset, offset + width)?
ref<Expr> ObjectState::modifiedAt(ref<Expr> offset, Expr::Width width) const {
  // Assumption: the root of the underlying array is the object at initial state.
  if (!updates.root) {
    assert(0 && "TPOT does not account for lazy intialization");
  }
  ref<Expr> res = ConstantExpr::create(0, Expr::Bool);
  ref<UpdateNode> cur = updates.head;
  while (cur) {
    // does the update overlap with [offset, offset + width)
    ref<Expr> overlap = AndExpr::create(
      UltExpr::create(
        cur->index,
        AddExpr::create(offset, ConstantExpr::create(width / 8, Expr::Int32))),
      UleExpr::create(
        offset,
        cur->index));

    res = OrExpr::create(res, overlap);

    cur = cur->next;
  }
  return res;
}

/***/

const UpdateList &SytSSObjectState::getUpdates(bool ignoreWrites) const {
  if (!updates.root) {
    assert(0);
  }

  if (!ignoreWrites) {
    return updates;
  } 
  return *(new UpdateList(updates.root, nullptr));
}

ref<Expr> SytSSObjectState::read(ref<Expr> offset, Expr::Width width, bool ignoreWrites) const {
  offset = adjustOffsetWidth(offset);

  // // Check for reads at constant offsets.
  // if (ConstantExpr *CE = dyn_cast<ConstantExpr>(offset))
  //   return read(CE->getZExtValue(32), width);

  // assert(!isBitVec && "bitvec read not supported at a symbolic offset");

  // Treat bool specially, it is the only non-byte sized write we allow.
  if (width == Expr::Bool)
    return ExtractExpr::create(read8(offset, ignoreWrites), 0, Expr::Bool);

  // Otherwise, follow the slow general case.
  unsigned NumBytes = width / 8;
  assert(width == NumBytes * 8 && "Invalid read size!");
  ref<Expr> Res(0);
  for (unsigned i = 0; i != NumBytes; ++i) {
    unsigned idx = Context::get().isLittleEndian() ? i : (NumBytes - i - 1);
    ref<Expr> Byte = read8(AddExpr::create(offset, 
                                           ConstantExpr::create(idx, 
                                                                Expr::Int32)), ignoreWrites);
    Res = i ? ConcatExpr::create(Byte, Res) : Byte;
  }

  return Res;
}

ref<Expr> SytSSObjectState::read8(ref<Expr> offset, bool ignoreWrites) const {
  // assert(!isa<ConstantExpr>(offset) && "constant offset passed to symbolic read8");
  // unsigned base, size;
  // fastRangeCheckOffset(offset, &base, &size);
  // flushRangeForRead(base, size);

  // if (size>4096) {
  //   std::string allocInfo;
  //   object->getAllocInfo(allocInfo);
  //   klee_warning_once(0, "flushing %d bytes on read, may be slow and/or crash: %s", 
  //                     size,
  //                     allocInfo.c_str());
  // }
  // offset = adjustOffsetWidth(offset);
  return ReadExpr::create(getUpdates(ignoreWrites), offset);
}

void SytSSObjectState::write(ref<Expr> offset, ref<Expr> value) {
  // Truncate offset to 32-bits.
  // offset = ZExtExpr::create(offset, Expr::Int32);

  // // Check for writes at constant offsets.
  // if (ConstantExpr *CE = dyn_cast<ConstantExpr>(offset)) {
  //   write(CE->getZExtValue(32), value);
  //   return;
  // }

  // // Treat bool specially, it is the only non-byte sized write we allow.
  Expr::Width w = value->getWidth();
  // if (w == Expr::Bool) {
  //   write8(offset, ZExtExpr::create(value, Expr::Int8));
  //   return;
  // }

  // Otherwise, follow the slow general case.
  unsigned NumBytes = w / 8;
  assert(w == NumBytes * 8 && "Invalid write size!");
  for (unsigned i = 0; i != NumBytes; ++i) {
    unsigned idx = Context::get().isLittleEndian() ? i : (NumBytes - i - 1);
    write8(AddExpr::create(offset, ConstantExpr::create(idx, Expr::Int64)),
           ExtractExpr::create(value, 8 * i, Expr::Int8));
  }
}

void SytSSObjectState::write8(ref<Expr> offset, ref<Expr> value) {
  // assert(!isa<ConstantExpr>(offset) && "constant offset passed to symbolic write8");
  // unsigned base, size;
  // fastRangeCheckOffset(offset, &base, &size);
  // flushRangeForWrite(base, size);

  // if (size>4096) {
  //   std::string allocInfo;
  //   object->getAllocInfo(allocInfo);
  //   klee_warning_once(0, "flushing %d bytes on read, may be slow and/or crash: %s", 
  //                     size,
  //                     allocInfo.c_str());
  // }
  
  updates.extend(adjustOffsetWidth(offset), value);
}