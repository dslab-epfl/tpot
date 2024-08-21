//===-- KQueryLoggingSolver.cpp -----------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "QueryLoggingSolver.h"

#include "klee/Expr/Expr.h"
#include "klee/Expr/ExprPPrinter.h"
#include "klee/System/Time.h"
#include "klee/Support/ErrorHandling.h"

using namespace klee;

class KQueryLoggingSolver : public QueryLoggingSolver {

private :
    ExprPPrinter *printer;

    virtual void printQuery(const Query& query,
                            const Query* falseQuery = 0,
                            const std::vector<const Array*>* arr_objects = 0,
                            const std::vector<const BitVecExpr*>* bv_objects = 0) {
        // TODO: this will not log symbolic bitvectors correctly

        const ref<Expr>* evalExprsBegin = 0;
        const ref<Expr>* evalExprsEnd = 0;

        if (0 != falseQuery) {
            evalExprsBegin = &query.expr;
            evalExprsEnd = &query.expr + 1;
        }

        const Array* const *evalArraysBegin = 0;
        const Array* const *evalArraysEnd = 0;

        if ((0 != arr_objects) && (false == arr_objects->empty())) {
            evalArraysBegin = &((*arr_objects)[0]);
            evalArraysEnd = &((*arr_objects)[0]) + arr_objects->size();
        }

        const Query* q = (0 == falseQuery) ? &query : falseQuery;

        printer->printQuery(logBuffer, q->constraints, q->expr,
                            evalExprsBegin, evalExprsEnd,
                            evalArraysBegin, evalArraysEnd);
    }

public:
    KQueryLoggingSolver(Solver *_solver, std::string path, time::Span queryTimeToLog, bool logTimedOut)
    : QueryLoggingSolver(_solver, path, "#", queryTimeToLog, logTimedOut),
    printer(ExprPPrinter::create(logBuffer)) {
    }

    virtual ~KQueryLoggingSolver() {
        delete printer;
    }
};

///

Solver *klee::createKQueryLoggingSolver(Solver *_solver, std::string path,
                                    time::Span minQueryTimeToLog, bool logTimedOut) {
  klee_warning("SyT's query logging solvers currently don't handle bitvectors correctly");
  return new Solver(new KQueryLoggingSolver(_solver, path, minQueryTimeToLog, logTimedOut));
}

