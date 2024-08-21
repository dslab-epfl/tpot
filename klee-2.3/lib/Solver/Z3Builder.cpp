//===-- Z3Builder.cpp ------------------------------------------*- C++ -*-====//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#include "klee/Config/config.h"
#ifdef ENABLE_Z3
#include "Z3Builder.h"

#include "klee/ADT/Bits.h"
#include "klee/Expr/Expr.h"
#include "klee/Solver/Solver.h"
#include "klee/Solver/SolverStats.h"
#include "klee/Support/ErrorHandling.h"

#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/CommandLine.h"

using namespace klee;

namespace {
llvm::cl::opt<bool> UseConstructHashZ3(
    "use-construct-hash-z3",
    llvm::cl::desc("Use hash-consing during Z3 query construction (default=true)"),
    llvm::cl::init(true),
    llvm::cl::cat(klee::ExprCat));

// FIXME: This should be std::atomic<bool>. Need C++11 for that.
bool Z3InterationLogOpen = false;
}

namespace klee {

// Declared here rather than `Z3Builder.h` so they can be called in gdb.
template <> void Z3NodeHandle<Z3_sort>::dump() {
  llvm::errs() << "Z3SortHandle:\n" << ::Z3_sort_to_string(context, node)
               << "\n";
}
template <> void Z3NodeHandle<Z3_ast>::dump() {
  llvm::errs() << "Z3ASTHandle:\n" << ::Z3_ast_to_string(context, as_ast())
               << "\n";
}

void custom_z3_error_handler(Z3_context ctx, Z3_error_code ec) {
  ::Z3_string errorMsg =
#ifdef USE_OLD_Z3
      // Z3 4.4.1
      Z3_get_error_msg(ec);
#else
      Z3_get_error_msg(ctx, ec);
#endif
  // FIXME: This is kind of a hack. The value comes from the enum
  // Z3_CANCELED_MSG but this isn't currently exposed by Z3's C API
  if (strcmp(errorMsg, "canceled") == 0) {
    // Solver timeout is not a fatal error
    return;
  }
  llvm::errs() << "Error: Incorrect use of Z3. [" << ec << "] " << errorMsg
               << "\n";
  // NOTE: The current implementation of `Z3_close_log()` can be safely
  // called even if the log isn't open.
  Z3_close_log();
  abort();
}

Z3ArrayExprHash::~Z3ArrayExprHash() {}

void Z3ArrayExprHash::clear() {
  _update_node_hash.clear();
  _array_hash.clear();
}

klee::Z3SortHandle Z3Builder::getArgumentSort(unsigned width) {
  if (width > 0) {
    return getBvSort((unsigned) width);
  } 
  // width == 0 represents a Z3 integer.
  return Z3SortHandle(Z3_mk_int_sort(ctx), ctx);
}

Z3Builder::Z3Builder(bool autoClearConstructCache, const char* z3LogInteractionFileArg)
    : autoClearConstructCache(autoClearConstructCache), z3LogInteractionFile("") {
  if (z3LogInteractionFileArg)
    this->z3LogInteractionFile = std::string(z3LogInteractionFileArg);
  if (z3LogInteractionFile.length() > 0) {
    klee_message("Logging Z3 API interaction to \"%s\"",
                 z3LogInteractionFile.c_str());
    assert(!Z3InterationLogOpen && "interaction log should not already be open");
    Z3_open_log(z3LogInteractionFile.c_str());
    Z3InterationLogOpen = true;
  }
  // FIXME: Should probably let the client pass in a Z3_config instead
  Z3_config cfg = Z3_mk_config();
  // It is very important that we ask Z3 to let us manage memory so that
  // we are able to cache expressions and sorts.
  ctx = Z3_mk_context_rc(cfg);
  // Make sure we handle any errors reported by Z3.
  Z3_set_error_handler(ctx, custom_z3_error_handler);
  // When emitting Z3 expressions make them SMT-LIBv2 compliant
  Z3_set_ast_print_mode(ctx, Z3_PRINT_SMTLIB2_COMPLIANT);
  Z3_del_config(cfg);

  // Declare the SMT functions Klee needs.
  for ( auto &f : smtFuncs ) {
    Z3_symbol name = Z3_mk_string_symbol(ctx, f.name.c_str());

    Z3SortHandle range = getArgumentSort(f.range);

    assert(f.argTypes.size() <= 3 && "FIXME: Support for functions with arity > 3 not implemented");

    Z3SortHandle arg1, arg2, arg3;
    if (f.argTypes.size() > 0) {
      arg1 = getArgumentSort(f.argTypes[0]);
      if (f.argTypes.size() > 1) {
        arg2 = getArgumentSort(f.argTypes[1]);
        if (f.argTypes.size() > 2) {
          arg3 = getArgumentSort(f.argTypes[2]);
        }
      }
    }

    ::Z3_sort domain[3] = {arg1, 0, 0};

    Z3_func_decl decl = Z3_mk_func_decl(ctx, name, f.argTypes.size(), domain, range);
    Z3_inc_ref(ctx, Z3_func_decl_to_ast(ctx, decl));
    f.z3_decl[&ctx] = decl;

    // TODO: treat tpot_bv2int as a regular function. We shouldn't need these..
    if (f.name == "tpot_bv2int") {
      tpot_bv2int_decl = decl;
    }
  }
}

Z3Builder::~Z3Builder() {
  // Clear caches so exprs/sorts gets freed before the destroying context
  // they are associated with.
  clearConstructCache();
  _arr_hash.clear();
  constant_array_assertions.clear();
  constructed_bitvecs.clear();
  constructed_ints.clear();

  for ( auto &f : smtFuncs ) {
    Z3_dec_ref(ctx, Z3_func_decl_to_ast(ctx, f.z3_decl[&ctx]));
  }

  Z3_del_context(ctx);
  if (z3LogInteractionFile.length() > 0) {
    Z3_close_log();
    Z3InterationLogOpen = false;
  }
}

Z3SortHandle Z3Builder::getBvSort(unsigned width) {
  // FIXME: cache these
  return Z3SortHandle(Z3_mk_bv_sort(ctx, width), ctx);
}

Z3SortHandle Z3Builder::getArraySort(Z3SortHandle domainSort,
                                     Z3SortHandle rangeSort) {
  // FIXME: cache these
  return Z3SortHandle(Z3_mk_array_sort(ctx, domainSort, rangeSort), ctx);
}

Z3ASTHandle Z3Builder::buildArray(const char *name, unsigned indexWidth,
                                  unsigned valueWidth) {
  Z3SortHandle domainSort = getArgumentSort(indexWidth);
  Z3SortHandle rangeSort = getArgumentSort(valueWidth);
  Z3SortHandle t = getArraySort(domainSort, rangeSort);
  Z3_symbol s = Z3_mk_string_symbol(ctx, const_cast<char *>(name));
  return Z3ASTHandle(Z3_mk_const(ctx, s, t), ctx);
}

Z3ASTHandle Z3Builder::getTrue() { return Z3ASTHandle(Z3_mk_true(ctx), ctx); }

Z3ASTHandle Z3Builder::getFalse() { return Z3ASTHandle(Z3_mk_false(ctx), ctx); }

Z3ASTHandle Z3Builder::bvOne(unsigned width) { return bvZExtConst(width, 1); }

Z3ASTHandle Z3Builder::bvZero(unsigned width) { return bvZExtConst(width, 0); }

Z3ASTHandle Z3Builder::bvMinusOne(unsigned width) {
  return bvSExtConst(width, (int64_t)-1);
}

Z3ASTHandle Z3Builder::bvConst32(unsigned width, uint32_t value) {
  Z3SortHandle t = getBvSort(width);
  return Z3ASTHandle(Z3_mk_unsigned_int(ctx, value, t), ctx);
}

Z3ASTHandle Z3Builder::bvConst64(unsigned width, uint64_t value) {
  Z3SortHandle t = getBvSort(width);
  return Z3ASTHandle(Z3_mk_unsigned_int64(ctx, value, t), ctx);
}

Z3ASTHandle Z3Builder::intConst(int64_t value) {
  Z3_sort t = Z3_mk_int_sort(ctx);
  return Z3ASTHandle(Z3_mk_int64(ctx, value, t), ctx);
}


Z3ASTHandle Z3Builder::bvZExtConst(unsigned width, uint64_t value) {
  if (width <= 64)
    return bvConst64(width, value);

  Z3ASTHandle expr = Z3ASTHandle(bvConst64(64, value), ctx);
  Z3ASTHandle zero = Z3ASTHandle(bvConst64(64, 0), ctx);
  for (width -= 64; width > 64; width -= 64)
    expr = Z3ASTHandle(Z3_mk_concat(ctx, zero, expr), ctx);
  return Z3ASTHandle(Z3_mk_concat(ctx, bvConst64(width, 0), expr), ctx);
}

Z3ASTHandle Z3Builder::bvSExtConst(unsigned width, uint64_t value) {
  if (width <= 64)
    return bvConst64(width, value);

  Z3SortHandle t = getBvSort(width - 64);
  if (value >> 63) {
    Z3ASTHandle r = Z3ASTHandle(Z3_mk_int64(ctx, -1, t), ctx);
    return Z3ASTHandle(Z3_mk_concat(ctx, r, bvConst64(64, value)), ctx);
  }

  Z3ASTHandle r = Z3ASTHandle(Z3_mk_int64(ctx, 0, t), ctx);
  return Z3ASTHandle(Z3_mk_concat(ctx, r, bvConst64(64, value)), ctx);
}

Z3ASTHandle Z3Builder::bvBoolExtract(Z3ASTHandle expr, int bit) {
  return Z3ASTHandle(Z3_mk_eq(ctx, bvExtract(expr, bit, bit), bvOne(1)), ctx);
}

Z3ASTHandle Z3Builder::bvExtract(Z3ASTHandle expr, unsigned top,
                                 unsigned bottom) {
  return Z3ASTHandle(Z3_mk_extract(ctx, top, bottom, expr), ctx);
}

Z3ASTHandle Z3Builder::eqExpr(Z3ASTHandle a, Z3ASTHandle b) {
  return Z3ASTHandle(Z3_mk_eq(ctx, a, b), ctx);
}

// logical right shift
Z3ASTHandle Z3Builder::bvRightShift(Z3ASTHandle expr, unsigned shift) {
  unsigned width = getBVLength(expr);

  if (shift == 0) {
    return expr;
  } else if (shift >= width) {
    return bvZero(width); // Overshift to zero
  } else {
    return Z3ASTHandle(
        Z3_mk_concat(ctx, bvZero(shift), bvExtract(expr, width - 1, shift)),
        ctx);
  }
}

// logical left shift
Z3ASTHandle Z3Builder::bvLeftShift(Z3ASTHandle expr, unsigned shift) {
  unsigned width = getBVLength(expr);

  if (shift == 0) {
    return expr;
  } else if (shift >= width) {
    return bvZero(width); // Overshift to zero
  } else {
    return Z3ASTHandle(
        Z3_mk_concat(ctx, bvExtract(expr, width - shift - 1, 0), bvZero(shift)),
        ctx);
  }
}

// left shift by a variable amount on an expression of the specified width
Z3ASTHandle Z3Builder::bvVarLeftShift(Z3ASTHandle expr, Z3ASTHandle shift) {
  // unsigned width = getBVLength(expr);
  // Z3ASTHandle res = bvZero(width);

  // // construct a big if-then-elif-elif-... with one case per possible shift
  // // amount
  // for (int i = width - 1; i >= 0; i--) {
  //   res =
  //       iteExpr(eqExpr(shift, bvConst32(width, i)), bvLeftShift(expr, i), res);
  // }

  // // If overshifting, shift to zero
  // Z3ASTHandle ex = bvLtExpr(shift, bvConst32(getBVLength(shift), width));
  // res = iteExpr(ex, res, bvZero(width));
  // return res;


  //? Unsure why Klee needed to use these expressions. Does z3's bvlshr not work?
  //? Does it not account for the size of the bitvector?
  return  Z3ASTHandle(Z3_mk_bvshl(ctx, expr, shift), ctx);
}

// logical right shift by a variable amount on an expression of the specified
// width
Z3ASTHandle Z3Builder::bvVarRightShift(Z3ASTHandle expr, Z3ASTHandle shift) {
  // unsigned width = getBVLength(expr);
  // Z3ASTHandle res = bvZero(width);

  // // construct a big if-then-elif-elif-... with one case per possible shift
  // // amount
  // for (int i = width - 1; i >= 0; i--) {
  //   res =
  //       iteExpr(eqExpr(shift, bvConst32(width, i)), bvRightShift(expr, i), res);
  // }

  // // If overshifting, shift to zero
  // Z3ASTHandle ex = bvLtExpr(shift, bvConst32(getBVLength(shift), width));
  // res = iteExpr(ex, res, bvZero(width));
  // return res;


  //? Unsure why Klee needed to use these expressions. Does z3's bvlshr not work?
  //? Does it not account for the size of the bitvector?
  return  Z3ASTHandle(Z3_mk_bvlshr(ctx, expr, shift), ctx);
}

// arithmetic right shift by a variable amount on an expression of the specified
// width
Z3ASTHandle Z3Builder::bvVarArithRightShift(Z3ASTHandle expr,
                                            Z3ASTHandle shift) {
  unsigned width = getBVLength(expr);

  // get the sign bit to fill with
  Z3ASTHandle signedBool = bvBoolExtract(expr, width - 1);

  // start with the result if shifting by width-1
  Z3ASTHandle res = constructAShrByConstant(expr, width - 1, signedBool);

  // construct a big if-then-elif-elif-... with one case per possible shift
  // amount
  // XXX more efficient to move the ite on the sign outside all exprs?
  // XXX more efficient to sign extend, right shift, then extract lower bits?
  for (int i = width - 2; i >= 0; i--) {
    res = iteExpr(eqExpr(shift, bvConst32(width, i)),
                  constructAShrByConstant(expr, i, signedBool), res);
  }

  // If overshifting, shift to zero
  Z3ASTHandle ex = bvLtExpr(shift, bvConst32(getBVLength(shift), width));
  res = iteExpr(ex, res, bvZero(width));
  return res;
}

Z3ASTHandle Z3Builder::notExpr(Z3ASTHandle expr) {
  return Z3ASTHandle(Z3_mk_not(ctx, expr), ctx);
}

Z3ASTHandle Z3Builder::bv2IntExpr(Z3ASTHandle expr) {
  ::Z3_ast args_arr[] = {expr}; 
  return Z3ASTHandle(Z3_mk_app(ctx, tpot_bv2int_decl, 1, args_arr), ctx);  
}

Z3ASTHandle Z3Builder::realInt2BVExpr(Z3ASTHandle expr) {
  return Z3ASTHandle(Z3_mk_int2bv(ctx, 64, expr), ctx);
}

Z3ASTHandle Z3Builder::bvNotExpr(Z3ASTHandle expr) {
  return Z3ASTHandle(Z3_mk_bvnot(ctx, expr), ctx);
}

Z3ASTHandle Z3Builder::andExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  ::Z3_ast args[2] = {lhs, rhs};
  return Z3ASTHandle(Z3_mk_and(ctx, 2, args), ctx);
}

Z3ASTHandle Z3Builder::bvAndExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  return Z3ASTHandle(Z3_mk_bvand(ctx, lhs, rhs), ctx);
}

Z3ASTHandle Z3Builder::orExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  ::Z3_ast args[2] = {lhs, rhs};
  return Z3ASTHandle(Z3_mk_or(ctx, 2, args), ctx);
}

Z3ASTHandle Z3Builder::bvOrExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  return Z3ASTHandle(Z3_mk_bvor(ctx, lhs, rhs), ctx);
}

Z3ASTHandle Z3Builder::iffExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  Z3SortHandle lhsSort = Z3SortHandle(Z3_get_sort(ctx, lhs), ctx);
  Z3SortHandle rhsSort = Z3SortHandle(Z3_get_sort(ctx, rhs), ctx);
  assert(Z3_get_sort_kind(ctx, lhsSort) == Z3_get_sort_kind(ctx, rhsSort) &&
         "lhs and rhs sorts must match");
  assert(Z3_get_sort_kind(ctx, lhsSort) == Z3_BOOL_SORT && "args must have BOOL sort");
  return Z3ASTHandle(Z3_mk_iff(ctx, lhs, rhs), ctx);
}

Z3ASTHandle Z3Builder::bvXorExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  return Z3ASTHandle(Z3_mk_bvxor(ctx, lhs, rhs), ctx);
}

Z3ASTHandle Z3Builder::bvSignExtend(Z3ASTHandle src, unsigned width) {
  unsigned src_width =
      Z3_get_bv_sort_size(ctx, Z3SortHandle(Z3_get_sort(ctx, src), ctx));
  assert(src_width <= width && "attempted to extend longer data");

  return Z3ASTHandle(Z3_mk_sign_ext(ctx, width - src_width, src), ctx);
}

Z3ASTHandle Z3Builder::writeExpr(Z3ASTHandle array, Z3ASTHandle index,
                                 Z3ASTHandle value) {
  return Z3ASTHandle(Z3_mk_store(ctx, array, index, value), ctx);
}

Z3ASTHandle Z3Builder::readExpr(Z3ASTHandle array, Z3ASTHandle index) {
  return Z3ASTHandle(Z3_mk_select(ctx, array, index), ctx);
}

Z3ASTHandle Z3Builder::iteExpr(Z3ASTHandle condition, Z3ASTHandle whenTrue,
                               Z3ASTHandle whenFalse) {
  return Z3ASTHandle(Z3_mk_ite(ctx, condition, whenTrue, whenFalse), ctx);
}

unsigned Z3Builder::getBVLength(Z3ASTHandle expr) {
  return Z3_get_bv_sort_size(ctx, Z3SortHandle(Z3_get_sort(ctx, expr), ctx));
}

Z3ASTHandle Z3Builder::bvLtExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  return Z3ASTHandle(Z3_mk_bvult(ctx, lhs, rhs), ctx);
}

Z3ASTHandle Z3Builder::bvLeExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  return Z3ASTHandle(Z3_mk_bvule(ctx, lhs, rhs), ctx);
}

Z3ASTHandle Z3Builder::sbvLtExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  return Z3ASTHandle(Z3_mk_bvslt(ctx, lhs, rhs), ctx);
}

Z3ASTHandle Z3Builder::sbvLeExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  return Z3ASTHandle(Z3_mk_bvsle(ctx, lhs, rhs), ctx);
}

Z3ASTHandle Z3Builder::intLtExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  return Z3ASTHandle(Z3_mk_lt(ctx, lhs, rhs), ctx);
}

Z3ASTHandle Z3Builder::intLeExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  return Z3ASTHandle(Z3_mk_le(ctx, lhs, rhs), ctx);
}

// Z3ASTHandle Z3Builder::intUltExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
//   Z3ASTHandle left_pos = intLeExpr(intConst(0), lhs);
//   Z3ASTHandle right_pos = intLeExpr(intConst(0), rhs);
//   Z3ASTHandle lt = Z3ASTHandle(Z3_mk_lt(ctx, lhs, rhs), ctx);

//   return andExpr(lt, andExpr(left_pos, right_pos));
// }

// Z3ASTHandle Z3Builder::intUleExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
//   Z3ASTHandle left_pos = intLeExpr(intConst(0), lhs);
//   Z3ASTHandle right_pos = intLeExpr(intConst(0), rhs);
//   Z3ASTHandle le = Z3ASTHandle(Z3_mk_le(ctx, lhs, rhs), ctx);

//   return andExpr(le, andExpr(left_pos, right_pos));
// }

Z3ASTHandle Z3Builder::constructAShrByConstant(Z3ASTHandle expr, unsigned shift,
                                               Z3ASTHandle isSigned) {
  unsigned width = getBVLength(expr);

  if (shift == 0) {
    return expr;
  } else if (shift >= width) {
    return bvZero(width); // Overshift to zero
  } else {
    // FIXME: Is this really the best way to interact with Z3?
    return iteExpr(isSigned,
                   Z3ASTHandle(Z3_mk_concat(ctx, bvMinusOne(shift),
                                            bvExtract(expr, width - 1, shift)),
                               ctx),
                   bvRightShift(expr, shift));
  }
}

Z3ASTHandle Z3Builder::getInitialArray(const Array *root) {

  assert(root);
  Z3ASTHandle array_expr;
  bool hashed = _arr_hash.lookupArrayExpr(root, array_expr);

  if (!hashed) {
    // Unique arrays by name, so we make sure the name is unique by
    // using the size of the array hash as a counter.
    std::string unique_id = llvm::utostr(_arr_hash._array_hash.size());

    std::string unique_name;
    // We need global variables' initial values to keep their names
    // so that constaraints translated from z3py can refer to them.
    // Global variable names should be unique anyway, otherwise the compiler
    // would complain.
    // TODO: this comment and the related code is outdated. Remove it.
    if (root->name.substr(0,13).compare("syt_initval__") == 0
        || root->name.substr(0,13).compare("syt_postval__") == 0)
      unique_name = root->name;
    else
      unique_name = root->name + unique_id;

    // if (root->getDomain() != Expr::Int32 || root->getRange() != Expr::Int8) {
    //   klee_error("SyT-Klee only supports arrays with domain Int32 and range Int8. ");
    // }

    array_expr = buildArray(unique_name.c_str(), root->getDomain(),
                            root->getRange());

    if (root->isConstantArray() && constant_array_assertions.count(root) == 0) {
      std::vector<Z3ASTHandle> array_assertions;
      for (unsigned i = 0, e = root->size; i != e; ++i) {
        // construct(= (select i root) root->value[i]) to be asserted in
        // Z3Solver.cpp
        int width_out;
        Z3ASTHandle array_value =
            construct(root->constantValues[i], &width_out);
        assert(width_out == (int)root->getRange() &&
               "Value doesn't match root range");
        array_assertions.push_back(
            eqExpr(readExpr(array_expr, bvConst32(root->getDomain(), i)),
                   array_value));
      }
      constant_array_assertions[root] = std::move(array_assertions);
    }

    _arr_hash.hashArrayExpr(root, array_expr);
  }

  return (array_expr);
}

Z3ASTHandle Z3Builder::getInitialRead(const Array *root, unsigned index) {
  if (root->getDomain() == 0) 
    return readExpr(getInitialArray(root), intConst(index));
  else 
    return readExpr(getInitialArray(root), bvConst32(32, index));
}

Z3ASTHandle Z3Builder::getBVHandle(std::string name, Expr::Width width) {
  auto find_res = constructed_bitvecs.find(name);
  if ( find_res != constructed_bitvecs.end())
    return find_res->second;

  Z3_symbol symb = Z3_mk_string_symbol(ctx, name.c_str());
  Z3_sort bv_sort = Z3_mk_bv_sort(ctx, width);
  
  Z3ASTHandle res = bitVecExpr(symb, bv_sort);
  constructed_bitvecs[name] = res;
  return res;
}

Z3ASTHandle Z3Builder::getIntHandle(std::string name) {
  auto find_res = constructed_ints.find(name);
  if ( find_res != constructed_ints.end())
    return find_res->second;

  Z3_symbol symb = Z3_mk_string_symbol(ctx, name.c_str());
  
  Z3ASTHandle res = intExpr(symb);
  constructed_ints[name] = res;
  return res;
}


Z3ASTHandle Z3Builder::getArrayForUpdate(const Array *root,
                                         const UpdateNode *un) {
  if (!un) {
    return (getInitialArray(root));
  } else {
    // FIXME: This really needs to be non-recursive.
    Z3ASTHandle un_expr;
    bool hashed = _arr_hash.lookupUpdateNodeExpr(un, un_expr);

    if (!hashed) {
      un_expr = writeExpr(getArrayForUpdate(root, un->next.get()),
                          construct(un->index, 0), construct(un->value, 0));

      _arr_hash.hashUpdateNodeExpr(un, un_expr);
    }

    return (un_expr);
  }
}

Z3ASTHandle Z3Builder::bitVecExpr(Z3_symbol symb, Z3_sort bv_sort)
{
  return Z3ASTHandle(Z3_mk_const(ctx, symb, bv_sort), ctx);
}

Z3ASTHandle Z3Builder::intExpr(Z3_symbol symb) {
  Z3_sort int_sort = Z3_mk_int_sort(ctx);
  return Z3ASTHandle(Z3_mk_const(ctx, symb, int_sort), ctx);
}

Z3ASTHandle Z3Builder::arrayEqExpr(Z3ASTHandle a, Z3ASTHandle b)
{
  return Z3ASTHandle(Z3_mk_eq(ctx, a, b), ctx);
}

Z3ASTHandle mk_var(Z3_context ctx, const char * name, Z3_sort ty)
{
  Z3_symbol   s  = Z3_mk_string_symbol(ctx, name);
  return Z3ASTHandle(Z3_mk_const(ctx, s, ty), ctx);
}

Z3ASTHandle Z3Builder::funcAppExpr(Z3_func_decl f, std::vector<Z3ASTHandle> args)
{
assert(args.size() <= 3 && "FIXME: Support for functions with arity > 3 not implemented");

Z3ASTHandle arg1, arg2, arg3;
if (args.size() > 0) {
  arg1 = args[0];
  if (args.size() > 1) {
    arg2 = args[1];
    if (args.size() > 2) {
      arg3 = args[2];
    }
  }
}

::Z3_ast args_arr[3] = {arg1, arg2, arg3};

return Z3ASTHandle(Z3_mk_app(ctx, f, args.size(), args_arr), ctx);  
}

Z3ASTHandle Z3Builder::forallExpr(unsigned int weight, unsigned int num_bound_vars, Z3_ast body, Z3_app bound_vars[]) {
  Z3_ast axiom = Z3_mk_forall_const(ctx, weight, num_bound_vars, bound_vars, 0, 0, body);
  return Z3ASTHandle(axiom, ctx);
}

Z3ASTHandle Z3Builder::existsExpr(unsigned int weight, unsigned int num_bound_vars, Z3_ast body, Z3_app bound_vars[]) { 
  Z3_ast axiom = Z3_mk_exists_const(ctx, weight, num_bound_vars, bound_vars, 0, 0, body);
  return Z3ASTHandle(axiom, ctx);
}

/** if *width_out!=1 then result is a bitvector,
    otherwise it is a bool */
Z3ASTHandle Z3Builder::construct(ref<Expr> e, int *width_out) {
  // TODO: We could potentially use Z3_simplify() here
  // to store simpler expressions.
  if (!UseConstructHashZ3 || isa<ConstantExpr>(e)) {
    return constructActual(e, width_out);
  } else {
    ExprHashMap<std::pair<Z3ASTHandle, unsigned> >::iterator it =
        constructed.find(e);
    if (it != constructed.end()) {
      if (width_out)
        *width_out = it->second.second;
      return it->second.first;
    } else {
      int width;
      if (!width_out)
        width_out = &width;
      Z3ASTHandle res = constructActual(e, width_out);
      constructed.insert(std::make_pair(e, std::make_pair(res, *width_out)));
      return res;
    }
  }
}

#define OVERLOADED_BINOP(op ,l, r) \
  Z3ASTHandle res;                                                  \
  if (*width_out == 0) {                                            \
    Z3_ast args[] = {l, r}; unsigned num_args = 2;                  \
    res = Z3ASTHandle(Z3_mk_##op(ctx, num_args, args), ctx);        \
  } else {                                                          \
    res = Z3ASTHandle(Z3_mk_bv##op(ctx, l, r), ctx);                \
    assert(getBVLength(res) == static_cast<unsigned>(*width_out) && \
          "width mismatch");                                        \
  }                                                                 \
  return res;

#define OVERLOADED_BINOP_2(op_bv, op_int, l, r) \
  Z3ASTHandle res;                                                  \
  if (*width_out == 0) {                                            \
    res = Z3ASTHandle(Z3_mk_##op_int(ctx, l, r), ctx);              \
  } else {                                                          \
    res = Z3ASTHandle(Z3_mk_bv##op_bv(ctx, l, r), ctx);             \
    assert(getBVLength(res) == static_cast<unsigned>(*width_out) && \
          "width mismatch");                                        \
  }                                                                 \
  return res;

/** if *width_out==0 then result is an integer,
    if *width_out!=1 then result is a bitvector,
    otherwise it is a bool */
Z3ASTHandle Z3Builder::constructActual(ref<Expr> e, int *width_out) {
  int width;
  if (!width_out)
    width_out = &width;

  ++stats::queryConstructs;

  switch (e->getKind()) {
  case Expr::Constant: {
    ConstantExpr *CE = cast<ConstantExpr>(e);
    *width_out = CE->getWidth();

    if (*width_out == 0)
      return intConst(CE->getSExtValue());

    // Coerce to bool if necessary.
    if (*width_out == 1)
      return CE->isTrue() ? getTrue() : getFalse();

    // Fast path.
    if (*width_out <= 32)
      return bvConst32(*width_out, CE->getZExtValue(32));
    if (*width_out <= 64)
      return bvConst64(*width_out, CE->getZExtValue());

    ref<ConstantExpr> Tmp = CE;
    Z3ASTHandle Res = bvConst64(64, Tmp->Extract(0, 64)->getZExtValue());
    while (Tmp->getWidth() > 64) {
      Tmp = Tmp->Extract(64, Tmp->getWidth() - 64);
      unsigned Width = std::min(64U, Tmp->getWidth());
      Res = Z3ASTHandle(
          Z3_mk_concat(ctx,
                       bvConst64(Width, Tmp->Extract(0, Width)->getZExtValue()),
                       Res),
          ctx);
    }
    return Res;
  }

  // Special
  case Expr::NotOptimized: {
    NotOptimizedExpr *noe = cast<NotOptimizedExpr>(e);
    return construct(noe->src, width_out);
  }

  case Expr::Read: {
    ReadExpr *re = cast<ReadExpr>(e);
    assert(re && re->updates.root);
    *width_out = re->updates.root->getRange();
    return readExpr(getArrayForUpdate(re->updates.root, re->updates.head.get()),
                    construct(re->index, 0));
  }

  case Expr::Select: {
    SelectExpr *se = cast<SelectExpr>(e);
    Z3ASTHandle cond = construct(se->cond, 0);
    Z3ASTHandle tExpr = construct(se->trueExpr, width_out);
    Z3ASTHandle fExpr = construct(se->falseExpr, width_out);
    return iteExpr(cond, tExpr, fExpr);
  }

  case Expr::Concat: {
    ConcatExpr *ce = cast<ConcatExpr>(e);
    unsigned numKids = ce->getNumKids();
    Z3ASTHandle res = construct(ce->getKid(numKids - 1), 0);
    for (int i = numKids - 2; i >= 0; i--) {
      res =
          Z3ASTHandle(Z3_mk_concat(ctx, construct(ce->getKid(i), 0), res), ctx);
    }
    *width_out = ce->getWidth();
    return res;
  }

  case Expr::Extract: {
    ExtractExpr *ee = cast<ExtractExpr>(e);
    Z3ASTHandle src = construct(ee->expr, width_out);
    *width_out = ee->getWidth();
    if (*width_out == 1) {
      return bvBoolExtract(src, ee->offset);
    } else {
      return bvExtract(src, ee->offset + *width_out - 1, ee->offset);
    }
  }

  // Casting

  case Expr::ZExt: {
    int srcWidth;
    CastExpr *ce = cast<CastExpr>(e);
    Z3ASTHandle src = construct(ce->src, &srcWidth);
    *width_out = ce->getWidth();
    if (srcWidth == 1) {
      return iteExpr(src, bvOne(*width_out), bvZero(*width_out));
    } else {
      assert(*width_out > srcWidth && "Invalid width_out");
      return Z3ASTHandle(Z3_mk_concat(ctx, bvZero(*width_out - srcWidth), src),
                         ctx);
    }
  }

  case Expr::SExt: {
    int srcWidth;
    CastExpr *ce = cast<CastExpr>(e);
    Z3ASTHandle src = construct(ce->src, &srcWidth);
    *width_out = ce->getWidth();
    if (srcWidth == 1) {
      return iteExpr(src, bvMinusOne(*width_out), bvZero(*width_out));
    } else {
      return bvSignExtend(src, *width_out);
    }
  }

  // Arithmetic
  case Expr::Add: {
    AddExpr *ae = cast<AddExpr>(e);
    Z3ASTHandle left = construct(ae->left, width_out);
    Z3ASTHandle right = construct(ae->right, width_out);
    assert(*width_out != 1 && "uncanonicalized add");
    OVERLOADED_BINOP(add, left, right);
  }

  case Expr::Sub: {
    SubExpr *se = cast<SubExpr>(e);
    Z3ASTHandle left = construct(se->left, width_out);
    Z3ASTHandle right = construct(se->right, width_out);
    assert(*width_out != 1 && "uncanonicalized sub");
    OVERLOADED_BINOP(sub, left, right);
  }

  case Expr::Mul: {
    MulExpr *me = cast<MulExpr>(e);
    Z3ASTHandle right = construct(me->right, width_out);
    assert(*width_out != 1 && "uncanonicalized mul");
    Z3ASTHandle left = construct(me->left, width_out);
    OVERLOADED_BINOP(mul, left, right);
  }

  case Expr::UDiv: {
    UDivExpr *de = cast<UDivExpr>(e);
    Z3ASTHandle left = construct(de->left, width_out);
    assert(*width_out != 1 && "uncanonicalized udiv");

    //! TPOT: disable for now.
    // if (ConstantExpr *CE = dyn_cast<ConstantExpr>(de->right)) {
    //   if (CE->getWidth() <= 64) {
    //     uint64_t divisor = CE->getZExtValue();
    //     if (bits64::isPowerOfTwo(divisor))
    //       return bvRightShift(left, bits64::indexOfSingleBit(divisor));
    //   }
    // }

    Z3ASTHandle right = construct(de->right, width_out);
    OVERLOADED_BINOP_2(udiv, div, left, right);
  }

  case Expr::SDiv: {
    SDivExpr *de = cast<SDivExpr>(e);
    Z3ASTHandle left = construct(de->left, width_out);
    assert(*width_out != 1 && "uncanonicalized sdiv");
    Z3ASTHandle right = construct(de->right, width_out);
    OVERLOADED_BINOP_2(sdiv, div, left, right);
  }

  case Expr::URem: {
    URemExpr *de = cast<URemExpr>(e);
    Z3ASTHandle left = construct(de->left, width_out);
    assert(*width_out != 1 && "uncanonicalized urem");

    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(de->right)) {
      if (CE->getWidth() <= 64 && *width_out != 0) {
        uint64_t divisor = CE->getZExtValue();

        if (bits64::isPowerOfTwo(divisor)) {
          // FIXME: This should be unsigned but currently needs to be signed to
          // avoid signed-unsigned comparison in assert.
          int bits = bits64::indexOfSingleBit(divisor);

          // special case for modding by 1 or else we bvExtract -1:0
          if (bits == 0) {
            return bvZero(*width_out);
          } else {
            assert(*width_out > bits && "invalid width_out");
            return Z3ASTHandle(Z3_mk_concat(ctx, bvZero(*width_out - bits),
                                            bvExtract(left, bits - 1, 0)),
                               ctx);
          }
        }
      }
    }

    

    Z3ASTHandle right = construct(de->right, width_out);
    OVERLOADED_BINOP_2(urem, rem, left, right);
  }

  case Expr::SRem: {
    SRemExpr *de = cast<SRemExpr>(e);
    Z3ASTHandle left = construct(de->left, width_out);
    Z3ASTHandle right = construct(de->right, width_out);
    assert(*width_out != 1 && "uncanonicalized srem");
    // LLVM's srem instruction says that the sign follows the dividend
    // (``left``).
    // Z3's C API says ``Z3_mk_bvsrem()`` does this so these seem to match.
    Z3ASTHandle result = Z3ASTHandle(Z3_mk_bvsrem(ctx, left, right), ctx);
    assert(getBVLength(result) == static_cast<unsigned>(*width_out) &&
           "width mismatch");
    return result;
  }

  // Bitwise
  case Expr::Not: {
    NotExpr *ne = cast<NotExpr>(e);
    Z3ASTHandle expr = construct(ne->expr, width_out);
    if (*width_out == 1) {
      return notExpr(expr);
    } else {
      return bvNotExpr(expr);
    }
  }

  case Expr::And: {
    AndExpr *ae = cast<AndExpr>(e);
    Z3ASTHandle left = construct(ae->left, width_out);
    Z3ASTHandle right = construct(ae->right, width_out);
    if (*width_out == 1) {
      return andExpr(left, right);
    } else {
      return bvAndExpr(left, right);
    }
  }

  case Expr::Or: {
    OrExpr *oe = cast<OrExpr>(e);
    Z3ASTHandle left = construct(oe->left, width_out);
    Z3ASTHandle right = construct(oe->right, width_out);
    if (*width_out == 1) {
      return orExpr(left, right);
    } else {
      return bvOrExpr(left, right);
    }
  }

  case Expr::Xor: {
    XorExpr *xe = cast<XorExpr>(e);
    Z3ASTHandle left = construct(xe->left, width_out);
    Z3ASTHandle right = construct(xe->right, width_out);

    if (*width_out == 1) {
      // XXX check for most efficient?
      return iteExpr(left, Z3ASTHandle(notExpr(right)), right);
    } else {
      return bvXorExpr(left, right);
    }
  }

  case Expr::Shl: {
    ShlExpr *se = cast<ShlExpr>(e);
    Z3ASTHandle left = construct(se->left, width_out);
    assert(*width_out != 1 && "uncanonicalized shl");

    // if (ConstantExpr *CE = dyn_cast<ConstantExpr>(se->right)) {
    //   return bvLeftShift(left, (unsigned)CE->getLimitedValue());
    // } else {
      int shiftWidth;
      Z3ASTHandle amount = construct(se->right, &shiftWidth);
      return bvVarLeftShift(left, amount);
    // }
  }

  case Expr::LShr: {
    LShrExpr *lse = cast<LShrExpr>(e);
    Z3ASTHandle left = construct(lse->left, width_out);
    assert(*width_out != 1 && "uncanonicalized lshr");

    // if (ConstantExpr *CE = dyn_cast<ConstantExpr>(lse->right)) {
    //   return bvRightShift(left, (unsigned)CE->getLimitedValue());
    // } else {
      int shiftWidth;
      Z3ASTHandle amount = construct(lse->right, &shiftWidth);
      return bvVarRightShift(left, amount);
    // }
  }

  case Expr::AShr: {
    AShrExpr *ase = cast<AShrExpr>(e);
    Z3ASTHandle left = construct(ase->left, width_out);
    assert(*width_out != 1 && "uncanonicalized ashr");

    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(ase->right)) {
      unsigned shift = (unsigned)CE->getLimitedValue();
      Z3ASTHandle signedBool = bvBoolExtract(left, *width_out - 1);
      return constructAShrByConstant(left, shift, signedBool);
    } else {
      int shiftWidth;
      Z3ASTHandle amount = construct(ase->right, &shiftWidth);
      return bvVarArithRightShift(left, amount);
    }
  }

  // Comparison

  case Expr::Eq: {
    EqExpr *ee = cast<EqExpr>(e);
    Z3ASTHandle left = construct(ee->left, width_out);
    Z3ASTHandle right = construct(ee->right, width_out);
    if (*width_out == 1) {
      if (ConstantExpr *CE = dyn_cast<ConstantExpr>(ee->left)) {
        if (CE->isTrue())
          return right;
        
        return notExpr(right);
      } else {
        return iffExpr(left, right);
      }
    } else {
      *width_out = 1;
      return eqExpr(left, right);
    }
  }

  // For now, we use unsigned comparators for Z3 integers.
  case Expr::Ult: {
    UltExpr *ue = cast<UltExpr>(e);
    Z3ASTHandle left = construct(ue->left, width_out);
    Z3ASTHandle right = construct(ue->right, width_out);
    assert(*width_out != 1 && "uncanonicalized ult");

    Z3ASTHandle res;
    if (*width_out == 0) {
      // This is an integer comparison
      // res = intUltExpr(left, right);
      res = intLtExpr(left, right);
    } else {
      res = bvLtExpr(left, right);
    }

    *width_out = 1;
    return res;
  }
  
  case Expr::Ule: {
    UleExpr *ue = cast<UleExpr>(e);
    Z3ASTHandle left = construct(ue->left, width_out);
    Z3ASTHandle right = construct(ue->right, width_out);
    assert(*width_out != 1 && "uncanonicalized ule");

    Z3ASTHandle res;
    if (*width_out == 0) {
      // This is an integer comparison
      // res = intUleExpr(left, right);
      res = intLeExpr(left, right);
    } else {
      res = bvLeExpr(left, right);
    }

    *width_out = 1;
    return res;
  }

  case Expr::Slt: {
    SltExpr *se = cast<SltExpr>(e);
    Z3ASTHandle left = construct(se->left, width_out);
    Z3ASTHandle right = construct(se->right, width_out);
    assert(*width_out != 1 && "uncanonicalized slt");

    Z3ASTHandle res;
    if (*width_out == 0) {
      // This is an integer comparison
      res = intLtExpr(left, right);
    } else {
      res = sbvLtExpr(left, right);
    }

    *width_out = 1;
    return res;
  }

  case Expr::Sle: {
    SleExpr *se = cast<SleExpr>(e);
    Z3ASTHandle left = construct(se->left, width_out);
    Z3ASTHandle right = construct(se->right, width_out);
    assert(*width_out != 1 && "uncanonicalized sle");

    Z3ASTHandle res;
    if (*width_out == 0) {
      // This is an integer comparison
      res = intLeExpr(left, right);
    } else {
      res = sbvLeExpr(left, right);
    }

    *width_out = 1;
    return res;
  }

  case Expr::Int: {
    IntExpr *ie = cast<IntExpr>(e);
    
    // ie->getWidth() should return 0
    *width_out = ie->getWidth();

    return getIntHandle(ie->name);
  }

  case Expr::BitVec: {
    BitVecExpr *be = cast<BitVecExpr>(e);
    // This is technically fine, but probably a mistake.
    // We might choose to keep a single ASTHandle if re-construction is ever necessary
    // assert(constructed_bitvecs.find(bound_var_name) == constructed_bitvecs.end() 
    //     && "Reconstructing bitvec");
    
    *width_out = be->width;
    return getBVHandle(be->name, be->width);
  }

  case Expr::BV2Int: {
    BV2IntExpr *be = cast<BV2IntExpr>(e); 
    Z3ASTHandle bv = construct(be->expr, width_out);
    assert(*width_out == 64 && "bv2int only supported for 64-bit bitvectors");

    // be->getWidth() should return 0
    *width_out = be->getWidth();
    
    return bv2IntExpr(bv);
  }

  case Expr::RealInt2BV: {
    RealInt2BVExpr *rib = cast<RealInt2BVExpr>(e);
    Z3ASTHandle bv = construct(rib->expr, width_out);

    // be->getWidth() should return 0
    *width_out = rib->getWidth();

    return realInt2BVExpr(bv);
  }

  case Expr::ArrayEq: {
    ArrayEqExpr *ae = cast<ArrayEqExpr>(e);

    Z3ASTHandle l_ast = getArrayForUpdate(ae->l.root, ae->l.head.get());
    Z3ASTHandle r_ast = getArrayForUpdate(ae->r.root, ae->r.head.get());
    *width_out = 1;
    return arrayEqExpr(l_ast, r_ast);
  }

  case Expr::FuncApp: {
    FuncAppExpr *fae = cast<FuncAppExpr>(e);
    auto decl = fae->decl.z3_decl[&this->ctx];

    std::vector<Z3ASTHandle> args;
    for (auto &arg : fae->args) {
      args.push_back(construct(arg, width_out));
    }

    *width_out = fae->getWidth();

    return funcAppExpr(decl, args);
  }

  case Expr::Forall: {
    ForallExpr *fe = cast<ForallExpr>(e);
    *width_out = 1;
    Z3_ast bound_var = construct(fe->var, width_out);
    Z3_ast body = construct(fe->body, width_out);
    Z3_app bound_vars[] = {(Z3_app) bound_var};
    int num_bound_vars = 1;
    int weight = 0;
    return forallExpr(weight, num_bound_vars, body, bound_vars);    
  }

  case Expr::Exists: {
    ExistsExpr *ee = cast<ExistsExpr>(e);
    *width_out = 1;
    Z3_ast bound_var = construct(ee->var, width_out);
    Z3_ast body = construct(ee->body, width_out);
    Z3_app bound_vars[] = {(Z3_app) bound_var};
    int num_bound_vars = 1;
    int weight = 0;
    return existsExpr(weight, num_bound_vars, body, bound_vars); 
  }

// unused due to canonicalization
#if 0
  case Expr::Ne:
  case Expr::Ugt:
  case Expr::Uge:
  case Expr::Sgt:
  case Expr::Sge:
#endif

  default:
    assert(0 && "unhandled Expr type");
    return getTrue();
  }
}
}
#endif // ENABLE_Z3
