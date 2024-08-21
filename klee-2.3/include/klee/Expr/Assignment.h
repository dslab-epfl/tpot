//===-- Assignment.h --------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_ASSIGNMENT_H
#define KLEE_ASSIGNMENT_H

#include "klee/Expr/Constraints.h"
#include "klee/Expr/ExprEvaluator.h"
#include "klee/Support/ErrorHandling.h"
#include "klee/Solver/Solver.h" // for bitvec_ce_t

#include <map>

namespace klee {
  class Array;

  class Assignment {
  public:
    typedef std::map<const Array*, std::vector<unsigned char> > array_bindings_ty;
    typedef std::map<const BitVecExpr *, uint64_t> bitvec_bindings_ty;
    typedef std::map<const IntExpr *, uint64_t> int_bindings_ty;

    bool allowFreeValues;
    array_bindings_ty arr_bindings;
    bitvec_bindings_ty bv_bindings;
    int_bindings_ty int_bindings;
    
  public:
    Assignment(bool _allowFreeValues=false) 
      : allowFreeValues(_allowFreeValues) {}
    Assignment(const std::vector<const Array*> &arrays,
               std::vector< std::vector<unsigned char> > &arr_values,
               const std::vector<const BitVecExpr *> &bitvecs,
               std::vector<bitvec_ce_t> &bv_values,
               const std::vector<const IntExpr *> &ints,
               std::vector<int_ce_t> &int_values,
               bool _allowFreeValues=false) 
      : allowFreeValues(_allowFreeValues){
      assert(arrays.size() == arr_values.size() && "Size mismatch in Assignment");
      assert(bitvecs.size() == bv_values.size() && "Size mismatch in Assignment");
      assert(ints.size() == int_values.size() && "Size mismatch in Assignment");

      std::vector< std::vector<unsigned char> >::iterator arrValIt = 
        arr_values.begin();
      for (std::vector<const Array*>::const_iterator it = arrays.begin(),
             ie = arrays.end(); it != ie; ++it) {
        const Array *os = *it;
        std::vector<unsigned char> &arr = *arrValIt;
        arr_bindings.insert(std::make_pair(os, arr));
        ++arrValIt;
      }

      std::vector<bitvec_ce_t>::iterator bvValIt = 
        bv_values.begin();
      for (std::vector<const BitVecExpr *>::const_iterator it = bitvecs.begin(),
             ie = bitvecs.end(); it != ie; ++it) {
        const BitVecExpr *os = *it;
        uint64_t i = *bvValIt;
        bv_bindings.insert(std::make_pair(os, i));
        ++bvValIt;
      }

      std::vector<int_ce_t>::iterator intValIt = 
        int_values.begin();
      for (std::vector<const IntExpr *>::const_iterator it = ints.begin(),
             ie = ints.end(); it != ie; ++it) {
        const IntExpr *os = *it;
        uint64_t i = *intValIt;
        int_bindings.insert(std::make_pair(os, i));
        ++intValIt;
      }
    }
    
    ref<Expr> evaluate(const Array *mo, unsigned index) const;
    ref<Expr> evaluate(const BitVecExpr * bv) const;
    ref<Expr> evaluate(const IntExpr * ie) const;
    ref<Expr> evaluate(ref<Expr> e);
    ConstraintSet createConstraintsFromAssignment() const;

    template<typename InputIterator>
    bool satisfies(InputIterator begin, InputIterator end);
    void dump();
  };
  
  class AssignmentEvaluator : public ExprEvaluator {
    const Assignment &a;

  protected:
    ref<Expr> getInitialValue(const Array &mo, unsigned index) {
      return a.evaluate(&mo, index);
    }

    ref<Expr> getInitialValue(const BitVecExpr &bv) {
      return a.evaluate(&bv);
    }

    ref<Expr> getInitialValue(const IntExpr &ie) {
      return a.evaluate(&ie);
    }
    
  public:
    AssignmentEvaluator(const Assignment &_a) : a(_a) {}    
  };

  /***/

  inline ref<Expr> Assignment::evaluate(const Array *array, 
                                        unsigned index) const {
    assert(array);
    array_bindings_ty::const_iterator it = arr_bindings.find(array);
    if (it!=arr_bindings.end() && index<it->second.size()) {
      return ConstantExpr::alloc(it->second[index], array->getRange());
    } else {
      if (allowFreeValues) {
        return ReadExpr::create(UpdateList(array, ref<UpdateNode>(nullptr)),
                                ConstantExpr::alloc(index, array->getDomain()));
      } else {
        return ConstantExpr::alloc(0, array->getRange());
      }
    }
  }

  inline ref<Expr> Assignment::evaluate(const BitVecExpr *bv) const {
    assert(bv);
    bitvec_bindings_ty::const_iterator it = bv_bindings.find(bv);
    if (it!=bv_bindings.end()) {
      return ConstantExpr::alloc(it->second, bv->getWidth());
    } else {
      // assert(0 && "BitVector value not present in assignment");
      // The counterexample cache needs this to check assignments generated before
      // extra symbolic arrays and bvs have been created.
      return ConstantExpr::alloc(0, bv->getWidth());
    }
  } 

  inline ref<Expr> Assignment::evaluate(const IntExpr *ie) const {
    assert(ie);
    int_bindings_ty::const_iterator it = int_bindings.find(ie);
    if (it!=int_bindings.end()) {
      // TODO: Figure out what the width should be. 64 for now.
      return ConstantExpr::alloc(it->second, 64);
    } else {
      assert(0 && "Int value not present in assignment");
      // The counterexample cache needs this to check assignments generated before
      // extra symbolic arrays and bvs have been created.
      // return ConstantExpr::alloc(0, bv->getWidth());
    }
  } 

  inline ref<Expr> Assignment::evaluate(ref<Expr> e) { 
    AssignmentEvaluator v(*this);
    return v.visit(e); 
  }

  template<typename InputIterator>
  inline bool Assignment::satisfies(InputIterator begin, InputIterator end) {
    AssignmentEvaluator v(*this);
    for (; begin!=end; ++begin)
      if (!v.visit(*begin)->isTrue())
        return false;
    return true;
  }
}

#endif /* KLEE_ASSIGNMENT_H */
