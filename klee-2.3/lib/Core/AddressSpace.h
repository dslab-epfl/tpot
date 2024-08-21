//===-- AddressSpace.h ------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_ADDRESSSPACE_H
#define KLEE_ADDRESSSPACE_H

#include "Memory.h"

#include "klee/Expr/Expr.h"
#include "klee/ADT/ImmutableMap.h"
#include "klee/System/Time.h"

namespace klee {
  class ExecutionState;
  class MemoryObject;
  class ObjectState;
  class TimingSolver;

  template<class T> class ref;

  typedef std::pair<const MemoryObject*, const ObjectState*> ObjectPair;
  typedef std::vector<ObjectPair> ResolutionList;  

  /// Function object ordering MemoryObject's by address.
  struct MemoryObjectLT {
    bool operator()(const MemoryObject *a, const MemoryObject *b) const;
  };

  typedef ImmutableMap<const MemoryObject *, ref<ObjectState>, MemoryObjectLT>
      MemoryMap;

  class AddressSpace {
  private:
    /// Epoch counter used to control ownership of objects.
    mutable unsigned cowKey;

    /// Unsupported, use copy constructor
    AddressSpace &operator=(const AddressSpace &);

    /// Check if pointer `p` can point to the memory object in the
    /// given object pair.  If so, add it to the given resolution list.
    ///
    /// \return 1 iff the resolution is incomplete (`maxResolutions`
    /// is non-zero and it was reached, or a query timed out), 0 iff
    /// the resolution is complete (`p` can only point to the given
    /// memory object), and 2 otherwise.
    int checkPointerInObject(ExecutionState &state, TimingSolver *solver,
                             ref<Expr> p, const ObjectPair &op,
                             ResolutionList &rl, unsigned maxResolutions) const;

  public:
    /// The MemoryObject -> ObjectState map that constitutes the
    /// address space.
    ///
    /// The set of objects where o->copyOnWriteOwner == cowKey are the
    /// objects that we own.
    ///
    /// \invariant forall o in objects, o->copyOnWriteOwner <= cowKey
    MemoryMap objects;

    AddressSpace() : cowKey(1) {}
    AddressSpace(const AddressSpace &b) : cowKey(++b.cowKey), objects(b.objects) { }
    ~AddressSpace() {}

    /// Resolve address to an ObjectPair in result.
    /// \return true iff an object was found.
    virtual bool resolveOne(const ref<ConstantExpr> &address, 
                    ObjectPair &result) const;

    /// Resolve address to an ObjectPair in result.
    ///
    /// \param state The state this address space is part of.
    /// \param solver A solver used to determine possible 
    ///               locations of the \a address.
    /// \param address The address to search for.
    /// \param[out] result An ObjectPair this address can resolve to 
    ///               (when returning true).
    /// \return true iff an object was found at \a address.
    virtual bool resolveOne(ExecutionState &state, 
                    TimingSolver *solver,
                    ref<Expr> address,
                    ObjectPair &result,
                    bool &success) const;

    /// Resolve pointer `p` to a list of `ObjectPairs` it can point
    /// to. If `maxResolutions` is non-zero then no more than that many
    /// pairs will be returned.
    ///
    /// \return true iff the resolution is incomplete (`maxResolutions`
    /// is non-zero and it was reached, or a query timed out).
    virtual bool resolve(ExecutionState &state,
                 TimingSolver *solver,
                 ref<Expr> p,
                 ResolutionList &rl, 
                 unsigned maxResolutions=0,
                 time::Span timeout=time::Span(),
                 ref<Expr> extraConstraint=NULL) const;

    /***/
    /// Add a binding to the address space.

    virtual void bindObject(const MemoryObject *mo, ObjectState *os);

    /// Remove a binding from the address space.
    void unbindObject(const MemoryObject *mo);

    /// Lookup a binding from a MemoryObject.
    virtual const ObjectState *findObject(const MemoryObject *mo) const;

    /// \brief Obtain an ObjectState suitable for writing.
    ///
    /// This returns a writeable object state, creating a new copy of
    /// the given ObjectState if necessary. If the address space owns
    /// the ObjectState then this routine effectively just strips the
    /// const qualifier it.
    ///
    /// \param mo The MemoryObject to get a writeable ObjectState for.
    /// \param os The current binding of the MemoryObject.
    /// \return A writeable ObjectState (\a os or a copy).
    virtual ObjectState *getWriteable(const MemoryObject *mo, const ObjectState *os);

    /// Copy the concrete values of all managed ObjectStates into the
    /// actual system memory location they were allocated at.
    void copyOutConcretes();

    /// Copy the concrete values of all managed ObjectStates back from
    /// the actual system memory location they were allocated
    /// at. ObjectStates will only be written to (and thus,
    /// potentially copied) if the memory values are different from
    /// the current concrete values.
    ///
    /// \retval true The copy succeeded. 
    /// \retval false The copy failed because a read-only object was modified.
    bool copyInConcretes();

    /// Updates the memory object with the raw memory from the address
    ///
    /// @param mo The MemoryObject to update
    /// @param os The associated memory state containing the actual data
    /// @param src_address the address to copy from
    /// @return
    bool copyInConcrete(const MemoryObject *mo, const ObjectState *os,
                        uint64_t src_address);
  };


  // SyT: implement the heap separately from global objects and the stack
  // TODO: rename AddressSpace to GlobalsAndStack and create a common base class.
  // TODO: manage heap in a CoW-fashion similar to AddressSpace.
  // struct HeapObjectLT {
  //   bool operator()(const MemoryObject *a, const MemoryObject *b) const;
  // };
  // typedef ImmutableMap<const MemoryObject *, ref<ObjectState>, HeapObjectLT>
  //     HeapMap;
  class Heap: public AddressSpace {
  public:
    // Implementation of this map as a vector is not efficient.
    // ! This is for legacy reasons, change it soon.
    mutable std::vector<ObjectPair> heapObjects;
    std::vector<ForallZone *> fzones;
    mutable std::map<const ForallZone *, std::vector<const SytSSMemoryObject *>> fZoneChildren;
    
    // maps names to base, size pairs
    std::map<std::string, std::pair<ref<Expr>, ref<Expr>>> namesToObjects;
    ref<Expr> heap_end;

    mutable std::map<ref<Expr>, int> resolutionCache;
    mutable std::map<ref<Expr>, int> resolutionHints;

    bool has_unnamed_shortcut = false;

    Heap() : AddressSpace() {}
    
    // For now, we don't do CoW, so deep copy heapObjects.
    // We deep copy object states, but not the objects themselves.
    Heap(const Heap &b) : AddressSpace(b), 
    resolutionCache(b.resolutionCache), resolutionHints(b.resolutionHints) {
      for (auto &op : b.heapObjects) {
        // this is terrible..  What is the proper C++ way to do this?
        // I don't want to bother with writing a virtual clone() function.
        const SytSSObjectState *sos = dynamic_cast<const SytSSObjectState *>(op.second);
        if (sos) {
          SytSSObjectState *os = new SytSSObjectState(*sos);
          heapObjects.push_back(std::make_pair(op.first, os));
        } else {
          ObjectState *os = new ObjectState(*op.second);
          heapObjects.push_back(std::make_pair(op.first, os));
        }
      }
      fzones = b.fzones;
      fZoneChildren = b.fZoneChildren;
      heap_end = b.heap_end;
      namesToObjects = b.namesToObjects;
      has_unnamed_shortcut = b.has_unnamed_shortcut;
    }
    virtual const ObjectState *findObject(const MemoryObject *mo) const override;
    void bindObject(const MemoryObject *mo, ObjectState *os) override;

    bool resolveOne(const ref<ConstantExpr> &address, 
                ObjectPair &result) const override;

    bool resolveOne(ExecutionState &state, 
                    TimingSolver *solver,
                    ref<Expr> address,
                    ObjectPair &result,
                    bool &success) const override;

    bool resolve(ExecutionState &state,
                 TimingSolver *solver,
                 ref<Expr> p,
                 ResolutionList &rl, 
                 unsigned maxResolutions=0,
                 time::Span timeout=time::Span(),
                 ref<Expr> extraConstraint=NULL) const override;

    ObjectState *getWriteable(const MemoryObject *mo, const ObjectState *os) override;

    bool hasUnnamed() {
      return has_unnamed_shortcut;
    }

    bool checkForLeaks()  {
      if (!has_unnamed_shortcut) {
        klee_error("Checking for leaks before an API function has terminated");
      }
      bool res = false;
      for (auto &op : heapObjects) {
        const SytSSMemoryObject *mo = dynamic_cast<const SytSSMemoryObject *>(op.first);
        const SytSSObjectState *sos = dynamic_cast<const SytSSObjectState *>(op.second);
        assert(sos && "Only SytSSObjectState objects should be in the heap");
        if (mo->isTpotGlobalArray)
          continue;
        if (!sos->isFreed && sos->syt_name == "") {
          tpot_message("Leaked memory object: %s", op.first->name.c_str());
          res = true;
        }
      }
      return res;
    }

    // helpers
    static bool mayResolveTo(ExecutionState &state,  TimingSolver *solver, 
                             const MemoryObject *mo, ref<Expr> address, ref<Expr> extraConstraints = NULL);

  };
} // End klee namespace

#endif /* KLEE_ADDRESSSPACE_H */
