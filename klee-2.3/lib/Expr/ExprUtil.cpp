//===-- ExprUtil.cpp ------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Expr/ExprUtil.h"
#include "klee/Expr/Expr.h"
#include "klee/Expr/ExprHashMap.h"
#include "klee/Expr/ExprVisitor.h"

#include <set>

using namespace klee;

void klee::findReads(ref<Expr> e, 
                     bool visitUpdates,
                     std::vector< ref<ReadExpr> > &results) {
  // Invariant: \forall_{i \in stack} !i.isConstant() && i \in visited 
  std::vector< ref<Expr> > stack;
  ExprHashSet visited;
  std::set<const UpdateNode *> updates;
  
  if (!isa<ConstantExpr>(e)) {
    visited.insert(e);
    stack.push_back(e);
  }

  while (!stack.empty()) {
    ref<Expr> top = stack.back();
    stack.pop_back();

    if (ReadExpr *re = dyn_cast<ReadExpr>(top)) {
      // We memoized so can just add to list without worrying about
      // repeats.
      results.push_back(re);

      if (!isa<ConstantExpr>(re->index) &&
          visited.insert(re->index).second)
        stack.push_back(re->index);
      
      if (visitUpdates) {
        // XXX this is probably suboptimal. We want to avoid a potential
        // explosion traversing update lists which can be quite
        // long. However, it seems silly to hash all of the update nodes
        // especially since we memoize all the expr results anyway. So
        // we take a simple approach of memoizing the results for the
        // head, which often will be shared among multiple nodes.
        if (updates.insert(re->updates.head.get()).second) {
          for (const auto *un = re->updates.head.get(); un;
               un = un->next.get()) {
            if (!isa<ConstantExpr>(un->index) &&
                visited.insert(un->index).second)
              stack.push_back(un->index);
            if (!isa<ConstantExpr>(un->value) &&
                visited.insert(un->value).second)
              stack.push_back(un->value);
          }
        }
      }
    } else if (!isa<ConstantExpr>(top)) {
      Expr *e = top.get();
      for (unsigned i=0; i<e->getNumKids(); i++) {
        ref<Expr> k = e->getKid(i);
        if (!isa<ConstantExpr>(k) &&
            visited.insert(k).second)
          stack.push_back(k);
      }
    }
  }
}

///

namespace klee {

class SymbolicObjectFinder : public ExprVisitor {
protected:
  Action visitRead(const ReadExpr &re) {
    const UpdateList &ul = re.updates;

    // XXX should we memo better than what ExprVisitor is doing for us?
    for (const auto *un = ul.head.get(); un; un = un->next.get()) {
      visit(un->index);
      visit(un->value);
    }

    if (ul.root->isSymbolicArray())
      if (arr_results.insert(ul.root).second)
        arr_objects.push_back(ul.root);

    return Action::doChildren();
  }

  Action visitBitVec(const BitVecExpr &e) {
    if (bv_results.insert(&e).second)
      bv_objects.push_back(&e);

    return Action::doChildren();
  }

  Action visitInt(const IntExpr &e) {
    if (int_results.insert(&e).second)
      int_objects.push_back(&e);

    return Action::doChildren();
  }

public:
  std::set<const Array*> arr_results;
  std::vector<const Array*> &arr_objects;
  std::set<const BitVecExpr*> bv_results;
  std::vector<const BitVecExpr*> &bv_objects;
  std::set<const IntExpr*> int_results;
  std::vector<const IntExpr*> &int_objects;
  
  SymbolicObjectFinder(std::vector<const Array*> &_arr_objects,
                       std::vector<const BitVecExpr*> &_bv_objects,
                       std::vector<const IntExpr*> &_int_objects)
    : arr_objects(_arr_objects), bv_objects(_bv_objects), int_objects(_int_objects) {}
};

ExprVisitor::Action ConstantArrayFinder::visitRead(const ReadExpr &re) {
  const UpdateList &ul = re.updates;

  // FIXME should we memo better than what ExprVisitor is doing for us?
  for (const auto *un = ul.head.get(); un; un = un->next.get()) {
    visit(un->index);
    visit(un->value);
  }

  if (ul.root->isConstantArray()) {
    results.insert(ul.root);
  }

  return Action::doChildren();
}
}

template<typename InputIterator>
void klee::findSymbolicObjects(InputIterator begin, 
                               InputIterator end,
                               std::vector<const Array*> &arr_results,
                               std::vector<const BitVecExpr*> &bv_results,
                               std::vector<const IntExpr *> &int_results) {
  SymbolicObjectFinder of(arr_results, bv_results, int_results);
  for (; begin!=end; ++begin)
    of.visit(*begin);
}

void klee::findSymbolicObjects(ref<Expr> e,
                               std::vector<const Array*> &arr_results,
                               std::vector<const BitVecExpr*> &bv_results,
                               std::vector<const IntExpr *> &int_results) {
  findSymbolicObjects(&e, &e+1, arr_results, bv_results, int_results);
}

typedef std::vector< ref<Expr> >::iterator A;
template void klee::findSymbolicObjects<A>(A, A, std::vector<const Array*> &,
                                           std::vector<const BitVecExpr*> &,
                                           std::vector<const IntExpr *> &);

typedef std::set< ref<Expr> >::iterator B;
template void klee::findSymbolicObjects<B>(B, B, std::vector<const Array*> &,
                                           std::vector<const BitVecExpr*> &,
                                           std::vector<const IntExpr *> &);

class ArrayNameMulFinder : public ExprVisitor {
protected:
  // Bitvectors represent bound variables

  Action visitMul(const MulExpr &me) {
    if (found_multiple) {
      found_unique = false;
      return Action::skipChildren();
    }
    ConstantExpr *left_const = dyn_cast<ConstantExpr>(me.left);
    ConstantExpr *right_const = dyn_cast<ConstantExpr>(me.right);
    if (left_const) {
      BitVecExpr *right_bv = dyn_cast<BitVecExpr>(me.right);
      if (!right_bv || right_bv->getKind() == Expr::SExt) {
        if (SExtExpr *right_sext = dyn_cast<SExtExpr>(me.right)) {
          right_bv = dyn_cast<BitVecExpr>(right_sext->src);
        }
      }
      if (right_bv && *right_bv == *bound_var) {
        found_unique = true;
        coeff = left_const->getZExtValue();
      }
    } else if (right_const) {
      BitVecExpr *left_bv = dyn_cast<BitVecExpr>(me.left);
      if (!left_bv) {
        if (SExtExpr *left_sext = dyn_cast<SExtExpr>(me.left)) {
          left_bv = dyn_cast<BitVecExpr>(left_sext->src);
        }
      }
      if (left_bv && *left_bv == *bound_var) {
        found_unique = true;
        coeff = right_const->getZExtValue();
      }
    } 
    found_multiple = true;
    return Action::doChildren();
  }

public:
  bool &found_unique;
  ref<Expr> bound_var;
  unsigned &coeff;
  bool found_multiple;

  
  ArrayNameMulFinder(bool &_found_unique, unsigned &_coeff, ref<Expr> _bound_var)
    : found_unique(_found_unique), bound_var(_bound_var), coeff(_coeff) {
      found_multiple = false;
      found_unique = false;
    }
};

class FZoneArrayNameFinder : public ExprVisitor {
protected:
  Action visitRead(const ReadExpr &re) {
    ref<Expr> idx = re.index;
    bool found_unique;
    unsigned _coeff;
    ArrayNameMulFinder inner_finder(found_unique, _coeff, bound_var);
    inner_finder.visit(idx);

    if (found_unique) {
      if (array_names.size() == 0) {
        array_names.push_back(re.updates.root->name);
        coeff = _coeff;
      } else if (array_names.back() != re.updates.root->name)
        assert(0 && "Bound var indexes into multiple arrays");
    }
      
    return Action::doChildren();
  }

public:
  std::vector<std::string> &array_names;
  unsigned &coeff;
  ref<Expr> bound_var;
  
  FZoneArrayNameFinder(std::vector<std::string> &_array_names, unsigned &_coeff, ref<Expr> _bound_var)
    : array_names(_array_names), coeff(_coeff), bound_var(_bound_var) {}
};

class IdxMulFinder : public ExprVisitor {
protected:
  // Bitvectors represent bound variables

  Action visitMul(const MulExpr &me) {
    if (found_multiple) {
      assert(0 && "Multiple indexes into the target array");
    }
    ConstantExpr *left_const = dyn_cast<ConstantExpr>(me.left);
    ConstantExpr *right_const = dyn_cast<ConstantExpr>(me.right);
    if (left_const) {
      ref<Expr>right = me.right;
      if (right->getKind() == Expr::SExt) {
        if (SExtExpr *right_sext = dyn_cast<SExtExpr>(me.right)) {
          right= right_sext->src;
        }
      }
      if (right->getKind() == Expr::ZExt) {
        if (ZExtExpr *right_zext = dyn_cast<ZExtExpr>(me.right)) {
          right= right_zext->src;
        }
      }
      if (coeff != left_const->getZExtValue()) {
        assert(0 && "Wrong coefficient");
      }
      out_idx = right;
    } else if (right_const) {
      ref<Expr>left = me.left;
      if (left->getKind() == Expr::SExt) {
        if (SExtExpr *left_sext = dyn_cast<SExtExpr>(me.left)) {
          left = left_sext->src;
        }
      }
      if (left->getKind() == Expr::ZExt) {
        if (ZExtExpr *left_zext = dyn_cast<ZExtExpr>(me.left)) {
          left = left_zext->src;
        }
      }
      if (coeff != right_const->getZExtValue()) {
        assert(0 && "Wrong coefficient");
      }
      out_idx = left;
    } 
    found_multiple = true;
    return Action::doChildren();
  }

public:
  ref<Expr> &out_idx;
  unsigned coeff;
  bool found_multiple;

  
  IdxMulFinder(unsigned _coeff, ref<Expr> &_out_idx): out_idx(_out_idx), coeff(_coeff) {
    found_multiple = false;
  }
};


class FZoneIdxFinder : public ExprVisitor {
protected:
  bool isReadExprAtOffset(ref<Expr> e, const ReadExpr *base, ref<Expr> offset) {
    const ReadExpr *re = dyn_cast<ReadExpr>(e.get());
      
    // right now, all Reads are byte reads but some
    // transformations might change this
    if (!re || (re->getWidth() != Expr::Int8))
      return false;
      
    // Check if the index follows the stride. 
    // FIXME: How aggressive should this be simplified. The
    // canonicalizing builder is probably the right choice, but this
    // is yet another area where we would really prefer it to be
    // global or else use static methods.
    return SubExpr::create(re->index, base->index) == offset;
  }

  Action visitConcat(const ConcatExpr &ce) {
    // see if this is a large read encoded as a concat chain.
    const ReadExpr *base = dyn_cast<ReadExpr>(ce.getKid(0));

    // right now, all Reads are byte reads but some
    // transformations might change this
    if (!base || base->getWidth() != Expr::Int8)
      return Action::doChildren(); // not a concat chain

    // Get stride expr in proper index width.
    Expr::Width idxWidth = base->index->getWidth();
    ref<Expr> strideExpr = ConstantExpr::alloc(-1, idxWidth);
    ref<Expr> offset = ConstantExpr::create(0, idxWidth);

    ref<Expr> e = ce.getKid(1);

    // concat chains are unbalanced to the right
    while (e->getKind() == Expr::Concat) {
      offset = AddExpr::create(offset, strideExpr);
      if (!isReadExprAtOffset(e->getKid(0), base, offset))
        return Action::doChildren(); // not a concat chain
      e = e->getKid(1);
    }

    offset = AddExpr::create(offset, strideExpr);
    if (!isReadExprAtOffset(e, base, offset))
      return Action::doChildren(); // not a concat chain

    const ReadExpr *re = dyn_cast<ReadExpr>(e);
    assert(re);
    visitRead(*re);
    return Action::skipChildren();
  }

  Action visitRead(const ReadExpr &re) {
    std::string this_name = re.updates.root->name;
    if (this_name == name) {
      ref<Expr> idx = re.index;
      ref<Expr> out_idx;
      // see if the index is constant
      if(ConstantExpr *c_idx= dyn_cast<ConstantExpr>(idx)) {
        uint64_t offset = c_idx->getZExtValue();
        assert(offset % coeff == 0);
        out_idx = ConstantExpr::alloc(offset / coeff, idx->getWidth());
      } else {
        bool found_unique;
        IdxMulFinder inner_finder(coeff, out_idx);
        inner_finder.visit(idx);
      }

      if (idxs.size() == 0)
        idxs.push_back(out_idx);
      else if (idxs.back() != out_idx)
        assert(0 && "Multiple indexes into the target array");
    }
      
    return Action::doChildren();
  }

public:
  std::vector<ref<Expr>> &idxs;
  unsigned coeff;
  std::string name;
  
  FZoneIdxFinder(std::vector<ref<Expr>> &_idxs, unsigned _coeff, std::string _name)
    : idxs(_idxs), coeff(_coeff), name(_name) {}
};

ref<Expr> klee::getFZoneIdx(ref<Expr> addr, ref<Expr> fz_body, ref<Expr> fz_bound_var) {
  std::vector<std::string> array_names;
  unsigned coeff;
  FZoneArrayNameFinder arr_finder(array_names, coeff, fz_bound_var);
  arr_finder.visit(fz_body);
  assert(array_names.size() == 1 || array_names.size() == 0);
  if (array_names.size() == 1) {
    std::string name = array_names[0];
    std::vector<ref<Expr>> idxs;
    FZoneIdxFinder idx_finder(idxs, coeff, name);
    idx_finder.visit(addr);
    assert(idxs.size() == 1);
    return idxs[0];
  }
  // if array_names.size() == 0, addr, this is an fzone modeling an array.
  bool found_unique;
  ArrayNameMulFinder inner_finder(found_unique, coeff, fz_bound_var);
  inner_finder.visit(fz_body);
  assert(found_unique);

  ref<Expr> out_idx;
  IdxMulFinder idx_finder(coeff, out_idx);
  idx_finder.visit(addr);
  return out_idx;
}
