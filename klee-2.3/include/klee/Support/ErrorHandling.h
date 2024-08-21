//===-- ErrorHandling.h -----------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_ERRORHANDLING_H
#define KLEE_ERRORHANDLING_H

#ifdef __CYGWIN__
#ifndef WINDOWS
#define WINDOWS
#endif
#endif

#include <stdio.h>

namespace klee {

extern FILE *klee_warning_file;
extern FILE *klee_message_file;

/// Print "KLEE: ERROR: " followed by the msg in printf format and a
/// newline on stderr and to warnings.txt, then exit with an error.
void klee_error(const char *msg, ...)
    __attribute__((format(printf, 1, 2), noreturn));

/// Print "KLEE: " followed by the msg in printf format and a
/// newline on stderr and to messages.txt.
void klee_message(const char *msg, ...) __attribute__((format(printf, 1, 2)));

/// Print "KLEE: " followed by the msg in printf format and a
/// newline to messages.txt.
void klee_message_to_file(const char *msg, ...)
    __attribute__((format(printf, 1, 2)));

/// Print "KLEE: WARNING: " followed by the msg in printf format and a
/// newline on stderr and to warnings.txt.
void klee_warning(const char *msg, ...) __attribute__((format(printf, 1, 2)));

void tpot_message(const char *msg, ...) __attribute__((format(printf, 1, 2)));

void tpot_opt_debug(const char *msg, ...) __attribute__((format(printf, 1, 2)));

/// Print "KLEE: WARNING: " followed by the msg in printf format and a
/// newline on stderr and to warnings.txt. However, the warning is only
/// printed once for each unique (id, msg) pair (as pointers).
void klee_warning_once(const void *id, const char *msg, ...)
    __attribute__((format(printf, 2, 3)));
}

#ifdef TPOT_ENABLE_LOG_STEPS
    #define LOG_STEPS(...) tpot_message(__VA_ARGS__)
#else
    #define LOG_STEPS(msg, ...)
#endif

#ifdef TPOT_ENABLE_LOG_STEPS_VERBOSE
    #define LOG_STEPS_VERBOSE( ...) klee_message(__VA_ARGS__)
#else
    #define LOG_STEPS_VERBOSE(...)
#endif

#ifdef TPOT_ENABLE_LOG_MEMORY_RESOLUTION
    #define LOG_MEMORY_RESOLUTION(...) klee_message(__VA_ARGS__)
#else
    #define LOG_MEMORY_RESOLUTION(...)
#endif

#ifdef TPOT_ENABLE_LOG_SOLVER_TIME
    #define LOG_SOLVER_TIME(...) klee_message(__VA_ARGS__)
#else
    #define LOG_SOLVER_TIME(...)
#endif

#ifdef TPOT_ENABLE_LOG_SIMPLFIIERS
    #define LOG_SIMPLIFIER(...) tpot_opt_debug(__VA_ARGS__)
#else
    #define LOG_SIMPLIFIER(...)
#endif





#endif /* KLEE_ERRORHANDLING_H */
