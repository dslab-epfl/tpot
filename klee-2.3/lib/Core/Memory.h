//===-- Memory.h ------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_MEMORY_H
#define KLEE_MEMORY_H

#include "Context.h"
#include "TimingSolver.h"

#include "klee/Expr/Expr.h"

#include "llvm/ADT/StringExtras.h"
#include "llvm/IR/Function.h"

#include <string>
#include <vector>

namespace llvm {
  class Value;
}

namespace klee {

class ArrayCache;
class BitArray;
class ExecutionState;
class MemoryManager;
class Solver;

class ForallElemProperty{
public:
  ref<Expr> numElems;               // number of elements in the array
  // TODO: does this have to be concrete?
  unsigned  elemSize;               // size of each element in the array
  ref<Expr> arrayOffset;            // byte offset of the array from the base of the object
  llvm::Function *condFunc;         // the function describing the condition
  std::vector<ref<Expr>> extraArgs; // extra arguments to _cond_

  ref<Expr> placeholderCond;

  ForallElemProperty(ref<Expr> _arrayOffset, ref<Expr> _numElems, 
    unsigned _elemSize, llvm::Function *_condFunc, std::vector<ref<Expr>> _extraArgs)
    : numElems(_numElems), elemSize(_elemSize), arrayOffset(_arrayOffset), 
      condFunc(_condFunc), extraArgs(_extraArgs), placeholderCond(NULL) {}
};

class ForallZoneProperty{
public:
  ref<Expr> condition;
  llvm::Function *fptr;

  ForallZoneProperty(ref<Expr> _condition, llvm::Function *_fptr)
    : condition(_condition), fptr(_fptr) {}
};

class MemoryObject {
  friend class STPBuilder;
  friend class ObjectState;
  friend class ExecutionState;
  friend class ref<MemoryObject>;
  friend class ref<const MemoryObject>;

private:
  static int counter;
  /// @brief Required by klee::ref-managed objects
  mutable class ReferenceCounter _refCount;

public:
  unsigned id;
  uint64_t address;

  /// size in bytes
  unsigned size;
  mutable std::string name;

  bool isLocal;
  mutable bool isGlobal;
  bool isFixed;

  bool isUserSpecified;

  MemoryManager *parent;

  /// "Location" for which this memory object was allocated. This
  /// should be either the allocating instruction or the global object
  /// it was allocated for (or whatever else makes sense).
  const llvm::Value *allocSite;

  // NULL for regular objects. Objects allocated on the
  // unique heap have 0 as their address and a symbolic 
  // pointer for their uniqueHeapAddress
  mutable ref<Expr> uniqueHeapAddress;

  mutable bool accessed = false;

  mutable std::vector<ForallElemProperty *> forallElem;

  // DO NOT IMPLEMENT
  MemoryObject(const MemoryObject &b);
  MemoryObject &operator=(const MemoryObject &b);

public:
  // XXX this is just a temp hack, should be removed
  explicit
  MemoryObject(uint64_t _address) 
    : id(counter++),
      address(_address),
      size(0),
      isFixed(true),
      parent(NULL),
      allocSite(0) {
  }

  MemoryObject(uint64_t _address, unsigned _size, 
               bool _isLocal, bool _isGlobal, bool _isFixed,
               const llvm::Value *_allocSite,
               MemoryManager *_parent,
               ref<Expr> _uniqueHeapAddress = NULL)
    : id(counter++),
      address(_address),
      size(_size),
      name("unnamed"),
      isLocal(_isLocal),
      isGlobal(_isGlobal),
      isFixed(_isFixed),
      isUserSpecified(false),
      parent(_parent), 
      allocSite(_allocSite),
      uniqueHeapAddress(_uniqueHeapAddress),
      accessed(false) {
  }

  virtual ~MemoryObject();

  /// Get an identifying string for this allocation.
  void getAllocInfo(std::string &result) const;

  void setName(std::string name) const {
    this->name = name;
  }

  ref<ConstantExpr> getBaseExpr() const { 
    return ConstantExpr::create(address, Context::get().getPointerWidth());
  }
  ref<ConstantExpr> getSizeExpr() const { 
    return ConstantExpr::create(size, Context::get().getPointerWidth());
  }
  ref<Expr> getOffsetExpr(ref<Expr> pointer) const {
    return SubExpr::create(pointer, getBaseExpr());
  }
  ref<Expr> getBoundsCheckPointer(ref<Expr> pointer) const {
    return getBoundsCheckOffset(getOffsetExpr(pointer));
  }
  ref<Expr> getBoundsCheckPointer(ref<Expr> pointer, unsigned bytes) const {
    return getBoundsCheckOffset(getOffsetExpr(pointer), bytes);
  }

  ref<Expr> getBoundsCheckOffset(ref<Expr> offset) const {
    if (size==0) {
      return EqExpr::create(offset, 
                            ConstantExpr::alloc(0, Context::get().getPointerWidth()));
    } else {
      return UltExpr::create(offset, getSizeExpr());
    }
  }
  virtual ref<Expr> getBoundsCheckOffset(ref<Expr> offset,
                                         unsigned bytes) const {
    if (bytes <= size) {
      return AndExpr::create(
          UleExpr::create(
              ConstantExpr::alloc(0, Context::get().getPointerWidth()), offset),
          UltExpr::create(
              offset, ConstantExpr::alloc(size - bytes + 1,
                                          Context::get().getPointerWidth())));
    } else {
      return ConstantExpr::alloc(0, Expr::Bool);
    }
  }

  /// Compare this object with memory object b.
  /// \param b memory object to compare with
  /// \return <0 if this is smaller, 0 if both are equal, >0 if b is smaller
  int compare(const MemoryObject &b) const {
    // Short-cut with id
    if (id == b.id)
      return 0;
    if (address != b.address)
      return (address < b.address ? -1 : 1);

    if (size != b.size)
      return (size < b.size ? -1 : 1);

    if (allocSite != b.allocSite)
      return (allocSite < b.allocSite ? -1 : 1);

    return 0;
  }
};

class ObjectState {
private:
  friend class AddressSpace;
  friend class ref<ObjectState>;

  unsigned copyOnWriteOwner; // exclusively for AddressSpace

  /// @brief Required by klee::ref-managed objects
  class ReferenceCounter _refCount;

  /// @brief Holds all known concrete bytes
  uint8_t *concreteStore;

  /// @brief concreteMask[byte] is set if byte is known to be concrete
  BitArray *concreteMask;

  /// knownSymbolics[byte] holds the symbolic expression for byte,
  /// if byte is known to be symbolic
  ref<Expr> *knownSymbolics;

  /// unflushedMask[byte] is set if byte is unflushed
  /// mutable because may need flushed during read of const
  mutable BitArray *unflushedMask;

  

public:
  ref<const MemoryObject> object;
  
  // mutable because we may need flush during read of const
  mutable UpdateList updates;

  unsigned size;

  bool readOnly;

  std::string syt_name;

  bool isBitVec = false;
  ref<Expr> bitVecRepresentation;
  ref<Expr> old_bitVecRepresentation;

public:
  /// Create a new object state for the given memory object with concrete
  /// contents. The initial contents are undefined, it is the callers
  /// responsibility to initialize the object contents appropriately.
  ObjectState(const MemoryObject *mo);

  /// Create a new object state for the given memory object with symbolic
  /// contents.
  ObjectState(const MemoryObject *mo, const Array *array, bool useBVRepr = false);

  ObjectState(const ObjectState &os);
  virtual ~ObjectState();

  const MemoryObject *getObject() const { return object.get(); }

  void setReadOnly(bool ro) { readOnly = ro; }

  /// Make contents all concrete and zero
  void initializeToZero();

  /// Make contents all concrete and random
  void initializeToRandom();

  virtual ref<Expr> read(ref<Expr> offset, Expr::Width width, 
                                bool ignoreWrites) const;
  virtual ref<Expr> read(unsigned offset, Expr::Width width, bool ignoreWrites) const;
  virtual ref<Expr> read8(unsigned offset, bool ignoreWrites) const;

  virtual void write(unsigned offset, ref<Expr> value);
  virtual void write(ref<Expr> offset, ref<Expr> value);

  virtual void write8(unsigned offset, uint8_t value);
  void write16(unsigned offset, uint16_t value);
  void write32(unsigned offset, uint32_t value);
  void write64(unsigned offset, uint64_t value);
  void print() const;

  /* Try to name the object with name n. Fails if object already has a different name */
  bool name(std::string n);

  ref<Expr> modifiedAt(ref<Expr> offset, Expr::Width width) const;

  /*
    Looks at all the symbolic bytes of this object, gets a value for them
    from the solver and puts them in the concreteStore.
  */
  void flushToConcreteStore(TimingSolver *solver,
                            const ExecutionState &state) const;

  bool forceFlushToConcreteStore(TimingSolver *solver,
                                 ExecutionState &state) const;

  void makeConcrete();

  void makeSymbolic();

  uint8_t getConcrete(unsigned offset) const;

  virtual ref<Expr> read8(ref<Expr> offset, bool ignoreWrites) const;

  virtual void write8(ref<Expr> offset, ref<Expr> value);

  const UpdateList &getUpdates(bool ignoreWrites) const;

  virtual void write8(unsigned offset, ref<Expr> value);

protected:
  void fastRangeCheckOffset(ref<Expr> offset, unsigned *base_r, 
                            unsigned *size_r) const;
  void flushRangeForRead(unsigned rangeBase, unsigned rangeSize) const;
  void flushRangeForWrite(unsigned rangeBase, unsigned rangeSize);

  /// isByteConcrete ==> !isByteKnownSymbolic
  bool isByteConcrete(unsigned offset) const;

  /// isByteKnownSymbolic ==> !isByteConcrete
  bool isByteKnownSymbolic(unsigned offset) const;

  /// isByteUnflushed(i) => (isByteConcrete(i) || isByteKnownSymbolic(i))
  bool isByteUnflushed(unsigned offset) const;

  void markByteConcrete(unsigned offset);
  void markByteSymbolic(unsigned offset);
  void markByteFlushed(unsigned offset);
  void markByteUnflushed(unsigned offset);
  void setKnownSymbolic(unsigned offset, Expr *value);

  ref<Expr> adjustOffsetWidth(ref<Expr> offset) const;

  ArrayCache *getArrayCache() const;
};

/// @brief MemoryObject for objects with symbolic size
class SytSSMemoryObject: public MemoryObject {
public:
  mutable ref<Expr> symbolicSize;
  // TPot global arrays doo not need to be freed.
  bool isTpotGlobalArray  = false;
  
  SytSSMemoryObject(uint64_t _address, ref<Expr> _symbolicSize, 
               bool _isLocal, bool _isGlobal, bool _isFixed,
               const llvm::Value *_allocSite,
               MemoryManager *_parent,
               ref<Expr> _uniqueHeapAddress = NULL)
    : MemoryObject(_address, 0, _isLocal, _isGlobal, _isFixed,
                   _allocSite, _parent, _uniqueHeapAddress), symbolicSize(_symbolicSize){
    assert(symbolicSize->getWidth() == 0 && "Symbolic size must be 0-width (integer)");
    assert(!uniqueHeapAddress.isNull() && "uniqueHeapAddress must not be NULL");
    assert(uniqueHeapAddress->getWidth() == 0 && "uniqueHeapAddress must be 0-width (integer)");
  }

  ref<ConstantExpr> getSizeExpr() const { 
    assert(0 && "getSizeExpr() not supported for SytSSMemoryObject");
  }

  ref<Expr> getBoundsCheckOffset(ref<Expr> offset) const {
    assert(0 && "getBoundsCheckOffset() not supported for SytSSMemoryObject");
  }
  ref<Expr> getBoundsCheckOffset(ref<Expr> offset, unsigned bytes) const {
    return AndExpr::create(
      UleExpr::create(ConstantExpr::alloc(bytes, Context::get().getPointerWidth()), symbolicSize),
      AndExpr::create(
        UleExpr::create(ConstantExpr::alloc(0, Context::get().getPointerWidth()), offset),
        UleExpr::create(offset, 
          SubExpr::create(symbolicSize, ConstantExpr::alloc(bytes, Context::get().getPointerWidth())))
      )
    );
  }
  
  /// Compare this object with memory object b.
  /// \param b memory object to compare with
  /// \return <0 if this is smaller, 0 if both are equal, >0 if b is smaller
  int compare(const SytSSMemoryObject &b) const {
    // Short-cut with id
    if (id == b.id)
      return 0;
    if (address != b.address)
      return (address < b.address ? -1 : 1);

    if (allocSite != b.allocSite)
      return (allocSite < b.allocSite ? -1 : 1);

    return symbolicSize->compare(*b.symbolicSize);
  }

};

/// @brief ObjectState for objects with symbolic size
class SytSSObjectState: public ObjectState {
public:
  ref<Expr> symbolicSize;
  bool isFreed = false;

  SytSSObjectState(const SytSSMemoryObject *mo, const Array *array)
    : ObjectState(mo, array, false) {
      symbolicSize = mo->symbolicSize;
  }

  SytSSObjectState(const SytSSMemoryObject *mo)
    : ObjectState(mo) {
      symbolicSize = mo->symbolicSize;
  }

  SytSSObjectState(const SytSSObjectState &os)
    : ObjectState(os) {
      symbolicSize = os.symbolicSize;
      isFreed = os.isFreed;
  }

  ref<Expr> read(ref<Expr> offset, Expr::Width width, bool ignoreWrites) const override;
  ref<Expr> read8(ref<Expr> offset, bool ignoreWrites) const override;

  void write(ref<Expr> offset, ref<Expr> value) override;
  void write8(ref<Expr> offset, ref<Expr> value) override;

  const UpdateList &getUpdates(bool ignoreWrites) const;
};

static ref<Expr> fitsInBounds(ref<Expr> address, ref<Expr> bytes, ref<Expr> obj_base, ref<Expr> obj_size) {
  //! this case is tailored to the short path of chekHeapSafety, attempting to avoid an infinite recursion bug.
  if (address->getWidth() == 0 &&
    *address == *obj_base) {
    return UleExpr::create(bytes, obj_size);
  }

  return AndExpr::create(
    UleExpr::create(bytes, obj_size),
    AndExpr::create(
      UleExpr::create(obj_base, address),
      // We use sub expressions here to avoid overflow.
      // addr + bytes <= base + base_uniq_sz   <==>   addr - base <=  + base_uniq_sz - bytes
      UleExpr::create(
        SubExpr::create(address, obj_base),
        SubExpr::create(obj_size, bytes)
      )
    )
  );
}

class ForallZone {
public:
  ref<Expr> size;
  ref<Expr> bound_var;
  ref<Expr> addr;
  llvm::Function *addr_fptr;
  llvm::Function *size_fptr;
  ref<Expr> fZoneConstraint = NULL;
  std::string name;

  // todo: rename these fields. The code is hard to read as it is.
  // todo: make these fields const. These should be tracked in per-state ObjectState structures..
  mutable ForallZoneProperty *fzoneProperty = NULL;

  ForallZone(ref<Expr> _size, // size of objects body points to for each value of the quantified variable.
            ref<Expr> _bound_var,
            ref<Expr> _addr,
            llvm::Function *_addr_fptr,
            llvm::Function *_size_fptr,
            std::string _name) : 
                   size(_size),
                   bound_var(_bound_var),
                   addr(_addr),
                   addr_fptr(_addr_fptr),
                   size_fptr(_size_fptr),
                   name(_name) {
  }

  ref<Expr> getExcludesExpr(ref<Expr> memOpAddress, ref<Expr> memOpBytes) const {
    std::vector<ref<Expr>> unsignedExprs;
    ref<Expr> addr_int = BV2IntExpr::convert(addr, unsignedExprs);
    ref<Expr> size_int = BV2IntExpr::convert(size, unsignedExprs);

    ref<Expr> res = ForallExpr::create(bound_var,
      NotExpr::create(
        fitsInBounds(memOpAddress, memOpBytes, addr_int, size_int)
      )
    );

    // return the integer version. This is probably redundant... (res == convertConstraint(res))
    //! We don't need to learn unsignedness constraints here, right?
    return BV2IntExpr::convertConstraint(res, unsignedExprs);
  }
};

class SytFZoneObjectState: public SytSSObjectState {
public:
  Expr *fZoneConstraint = NULL;

  SytFZoneObjectState(const SytSSMemoryObject *mo, const Array *array)
    : SytSSObjectState(mo, array) {
  }

  SytFZoneObjectState(const SytSSMemoryObject *mo)
    : SytSSObjectState(mo) {
  }

  SytFZoneObjectState(const SytSSObjectState &os)
    : SytSSObjectState(os) {
  }
};
  
} // End klee namespace

#endif /* KLEE_MEMORY_H */
