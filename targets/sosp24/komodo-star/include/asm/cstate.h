#pragma once


/*
    This code is used by TPot to model the behavior in assembly code in C.
    TPot uses these models instead of assembly macros provided by Serval.
    This is because TPot interprets LLVM-IR, while Serval interprets assembly.
    These models are linked against cstate.c.
*/

extern unsigned long mhartid_cstate;
extern unsigned long mvendorid_cstate;
extern unsigned long mimpid_cstate;
extern unsigned long misa_cstate;
extern unsigned long marchid_cstate;
extern unsigned long mscratch_cstate;
extern unsigned long mcause_cstate;
extern unsigned long mtval_cstate;
extern unsigned long mepc_cstate;
extern unsigned long mstatus_cstate;
extern unsigned long mcounteren_cstate;
extern unsigned long medeleg_cstate;
extern unsigned long mideleg_cstate;

extern unsigned long sscratch_cstate;
extern unsigned long scause_cstate;
extern unsigned long stval_cstate;
extern unsigned long sepc_cstate;
extern unsigned long sstatus_cstate;
extern unsigned long satp_cstate;
extern unsigned long stvec_cstate;
extern unsigned long scounteren_cstate;
extern unsigned long sip_cstate;
extern unsigned long sie_cstate;

extern unsigned long pmpcfg0_cstate;
extern unsigned long pmpcfg2_cstate;
extern unsigned long pmpaddr2_cstate;
extern unsigned long pmpaddr3_cstate;
extern unsigned long pmpaddr4_cstate;
extern unsigned long pmpaddr5_cstate;

#define csr_swap(csr, val)                                      \
({                                                              \
        unsigned long __tmp = csr ## _cstate;                    \
        csr ## cstate = val;                                    \
        __tmp;                                                  \
})

#define csr_read(csr)                                    \
({                                                       \
        unsigned long __v = csr ## _cstate;               \
        __v;                                             \
})

#define csr_write(csr, val)                                     \
({                                                              \
        unsigned long __v = (unsigned long)(val);               \
        csr ## _cstate = __v;                                    \
})

#define csr_read_set(csr, val)                                  \
({                                                              \
        unsigned long __v = (unsigned long)( csr ## _cstate);    \
        csr ## _cstate = csr ## _cstate | val;                    \
        __v;                                                    \
})

#define csr_set(csr, val)                                 \
({                                                        \
        unsigned long __v = (unsigned long)(val);         \
        csr ## _cstate = csr ## _cstate | __v;              \
})

#define csr_read_clear(csr, val)                           \
({                                                         \
        unsigned long __v = (unsigned long)(csr##cstate);  \
        csr ## _cstate = csr## _cstate & (~val);                \
        __v;                                               \
})

#define csr_clear(csr, val)                               \
({                                                        \
        unsigned long __v = (unsigned long)(val);         \
        csr##_cstate = csr## _cstate  & (~__v);              \
})

#define csr_write_safe(csr, val)    csr_write(csr, val)