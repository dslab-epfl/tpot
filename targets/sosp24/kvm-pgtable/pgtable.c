/*SPEC*/ /*SYNTAX*/ //@rc::import pgtable_lemmas from refinedc.linux.casestudies.pgtable

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

/*TPOT*/ // use our assertion primitive instead of refinedc's
/*TPOT*/ //#include <refinedc.h>
/*TPOT*/ #include <tpot_primitives.h> // assert

typedef uint64_t u64;
typedef uint32_t u32;

#define PAGE_SHIFT        12
#define WRITE_ONCE(a, b)  ((a) = (b))
#define BITS_PER_LONG     (sizeof(long) * 8)
#define EINVAL            22  /* Invalid argument */
// TPot: fix definition of WARN_ON
// #define WARN_ON(b)        (assert(b))
#define WARN_ON(b)        (assert(!b))

/* linux/bits.h */

// #define BIT(i) (1UL << (i))
/*INTERNAL*/ /* [[rc::parameters("i : Z")]] */
/*INTERNAL*/ /* [[rc::args("i @ int<i32>")]] */
/*INTERNAL*/ /* [[rc::requires("{0 ≤ i < 64}")]] */
/*INTERNAL*/ /* [[rc::returns("{bf_mask_cons i 1 bf_nil} @ bitfield_raw<u64>")]] */
/*PROOF*/ /* [[rc::tactics("all: have ? := Z_shiftl_1_range i 64; try solve_goal.")]] */
/*PROOF*/ /* [[rc::lemmas("bf_mask_bit")]] */
u64 BIT(int i)
{
    return (1UL << (i));
}

/*
 * Create a contiguous bitmask starting at bit position @l and ending at
 * position @h. For example
 * GENMASK_ULL(39, 21) gives us the 64bit vector 0x000000ffffe00000.
 */
// #define GENMASK(h, l) \
    (((~0UL) - (1UL << (l)) + 1) & (~0UL >> (BITS_PER_LONG - 1 - (h))))
/*INTERNAL*/ /* [[rc::parameters("h : Z", "l : Z")]] */
/*INTERNAL*/ /* [[rc::args("h @ int<i32>", "l @ int<i32>")]] */
/*INTERNAL*/ /* [[rc::requires("{0 ≤ l}", "{l < h < 64}")]] */
/*INTERNAL*/ /* [[rc::returns("{bf_mask_cons l (h - l + 1) bf_nil} @ bitfield_raw<u64>")]] */
/*PROOF*/ /* [[rc::tactics("all: have [??] : 1 ≤ 1 ≪ l ≤ 2^64 - 1 by apply Z_shiftl_1_range; solve_goal.")]] */
/*PROOF*/ /* [[rc::tactics("all: try have -> : max_int u64 = 2^64 - 1 by solve_goal.")]] */
/*PROOF*/ /* [[rc::tactics("all: try have -> : ly_size i64 * 8 = bits_per_int u64 by solve_goal.")]] */
/*PROOF*/ /* [[rc::tactics("all: try have -> : bits_per_int u64 = 64 by solve_goal.")]] */
/*PROOF*/ /* [[rc::tactics("all: try have -> : Z_lunot 64 0 = 2^64 - 1 by solve_goal.")]] */
/*PROOF*/ /* [[rc::tactics("all: try solve_goal.")]] */
/*PROOF*/ /* [[rc::lemmas("bf_mask_gen")]] */
u64 GENMASK(int h, int l)
{
    return (((~0UL) - (1UL << (l)) + 1) & (~0UL >> (BITS_PER_LONG - 1 - (h))));
}

/* linux/bitfield.h */
#define __bf_shf(x) (__builtin_ffsll(x) - 1)

/**
 * FIELD_GET() - extract a bitfield element
 * @_mask: shifted mask defining the field's length and position
 * @_reg:  value of entire bitfield
 *
 * FIELD_GET() extracts the field specified by @_mask from the
 * bitfield passed in as @_reg by masking and shifting it down.
 */
/*
#define FIELD_GET(_mask, _reg)        \
    ({                                \
        __BF_FIELD_CHECK(_mask, _reg, 0U, "FIELD_GET: ");       \
        (typeof(_mask))(((_reg) & (_mask)) >> __bf_shf(_mask)); \
    })
*/
/*INTERNAL*/ /* [[rc::parameters("r : Z", "a : Z", "k : Z", "res : Z")]] */
/*INTERNAL*/ /* [[rc::args("{bf_mask_cons a k bf_nil} @ bitfield_raw<u64>", "r @ bitfield_raw<u64>")]] */
/*INTERNAL*/ /* [[rc::requires("{0 ≤ a}", "{0 < k}", "{a + k ≤ 64}")]] */
/*INTERNAL*/ /* [[rc::requires("{normalize_bitfield_eq (bf_slice a k r) res}")]] */
/*INTERNAL*/ /* [[rc::returns("res @ int<u64>")]] */
/*PROOF*/ /* [[rc::tactics("all: unfold normalize_bitfield_eq in *; subst.")]] */
/*PROOF*/ /* [[rc::tactics("all: try rewrite Z.add_simpl_r Z_least_significant_one_nonempty_mask.")]] */
/*PROOF*/ /* [[rc::tactics("all: try solve_goal.")]] */
/*PROOF*/ /* [[rc::lemmas("bf_mask_cons_singleton_nonempty", "bf_shr_singleton")]] */
u64 FIELD_GET(u64 _mask, u64 _reg)
{
    return (((_reg) & (_mask)) >> __bf_shf(_mask));
}

/**
 * FIELD_PREP() - prepare a bitfield element
 * @_mask: shifted mask defining the field's length and position
 * @_val:  value to put in the field
 *
 * FIELD_PREP() masks and shifts up the value.  The result should
 * be combined with other fields of the bitfield using logical OR.
 */
/*
#define FIELD_PREP(_mask, _val)                 \
    ({                                          \
        __BF_FIELD_CHECK(_mask, 0ULL, _val, "FIELD_PREP: ");     \
        ((typeof(_mask))(_val) << __bf_shf(_mask)) & (_mask);    \
    })
*/
/*INTERNAL*/ /* [[rc::parameters("a : Z", "k : Z", "v : Z")]] */
/*INTERNAL*/ /* [[rc::args("{bf_mask_cons a k bf_nil} @ bitfield_raw<u64>", "v @ int<u64>")]] */
/*INTERNAL*/ /* [[rc::requires("{0 ≤ a}", "{0 < k}", "{a + k ≤ 64}", "{0 ≤ v < 2^k}")]] */
/*INTERNAL*/ /* [[rc::returns("{bf_cons a k v bf_nil} @ bitfield_raw<u64>")]] */
/*PROOF*/ /* [[rc::tactics("all: have [??] : v ≤ v ≪ a ≤ 2^64 - 1 by apply (Z_shl_bound k _ _ _); solve_goal.")]] */
/*PROOF*/ /* [[rc::tactics("all: try have -> : max_int u64 = 2^64 - 1 by solve_goal.")]] */
/*PROOF*/ /* [[rc::tactics("all: try rewrite Z.add_simpl_r Z_least_significant_one_nonempty_mask ?bf_slice_shl.")]] */
/*PROOF*/ /* [[rc::tactics("all: try solve_goal.")]] */
/*PROOF*/ /* [[rc::lemmas("bf_mask_cons_singleton_nonempty")]] */
u64 FIELD_PREP(u64 _mask, u64 _val)
{
    return ((_val) << __bf_shf(_mask)) & (_mask);
}

/* asm/kvm_pgtable.h */

typedef u64 kvm_pte_t;
typedef u64 phys_addr_t;

/**
 * enum kvm_pgtable_prot - Page-table permissions and attributes.
 * @KVM_PGTABLE_PROT_X:         Execute permission.
 * @KVM_PGTABLE_PROT_W:         Write permission.
 * @KVM_PGTABLE_PROT_R:         Read permission.
 * @KVM_PGTABLE_PROT_DEVICE:    Device attributes.
 */
// enum kvm_pgtable_prot {
//     KVM_PGTABLE_PROT_X          = BIT(0),
//     KVM_PGTABLE_PROT_W          = BIT(1),
//     KVM_PGTABLE_PROT_R          = BIT(2),
//     KVM_PGTABLE_PROT_DEVICE     = BIT(3),
// };
typedef u64 kvm_pgtable_prot;
#define KVM_PGTABLE_PROT_X          BIT(0)
#define KVM_PGTABLE_PROT_W          BIT(1)
#define KVM_PGTABLE_PROT_R          BIT(2)
#define KVM_PGTABLE_PROT_DEVICE     BIT(3)

/**
 * struct kvm_pgtable_mm_ops - Memory management callbacks.
 * @zalloc_page: Allocate a zeroed memory page.
 * @zalloc_pages_exact: Allocate an exact number of zeroed memory pages.
 * @free_pages_exact: Free an exact number of memory pages.
 * @get_page: Increment the refcount on a page.
 * @put_page: Decrement the refcount on a page.
 * @page_count: Returns the refcount of a page.
 * @phys_to_virt: Convert a physical address into a virtual address.
 * @virt_to_phys: Convert a virtual address into a physical address.
 */
struct /*PROOF*/ /* [[rc::refined_by("mm_ops : mm_callbacks")]] */ kvm_pgtable_mm_ops {
  // void* (*zalloc_page)(void *arg);
  // void* (*zalloc_pages_exact)(size_t size);
  // void (*free_pages_exact)(void *addr, size_t size);
  // void (*get_page)(void *addr);
  // void (*put_page)(void *addr);
  // int (*page_count)(void *addr);
  // void* (*phys_to_virt)(phys_addr_t phys);
  /*PROOF*/ /* [[rc::field("function_ptr<{fn(∀ (p, a) : loc * Z; p @ &own (a @ int u64); True) → ∃ () : (), (mm_ops.(virt_to_phys) a) @ bitfield_raw u64; True}>")]] */
  phys_addr_t (*virt_to_phys)(void *addr);
};

/* asm/memory.h */

#define MT_NORMAL                           0
#define MT_DEVICE_nGnRE                     5

// pgtable.c

#define KVM_PGTABLE_MAX_LEVELS              4U
#define KVM_PTE_VALID                       BIT(0)
#define KVM_PTE_TYPE                        BIT(1)
#define KVM_PTE_TYPE_BLOCK                  0
#define KVM_PTE_TYPE_PAGE                   1
#define KVM_PTE_TYPE_TABLE                  1
#define KVM_PTE_ADDR_MASK                   GENMASK(47, PAGE_SHIFT)
#define KVM_PTE_ADDR_51_48                  GENMASK(15, 12)
#define KVM_PTE_LEAF_ATTR_LO                GENMASK(11, 2)
#define KVM_PTE_LEAF_ATTR_LO_S1_ATTRIDX     GENMASK(4, 2)
#define KVM_PTE_LEAF_ATTR_LO_S1_AP          GENMASK(7, 6)
#define KVM_PTE_LEAF_ATTR_LO_S1_AP_RO       3
#define KVM_PTE_LEAF_ATTR_LO_S1_AP_RW       1
#define KVM_PTE_LEAF_ATTR_LO_S1_SH          GENMASK(9, 8)
#define KVM_PTE_LEAF_ATTR_LO_S1_SH_IS       3
#define KVM_PTE_LEAF_ATTR_LO_S1_AF          BIT(10)
// #define KVM_PTE_LEAF_ATTR_LO_S2_MEMATTR     GENMASK(5, 2)
// #define KVM_PTE_LEAF_ATTR_LO_S2_S2AP_R      BIT(6)
// #define KVM_PTE_LEAF_ATTR_LO_S2_S2AP_W      BIT(7)
// #define KVM_PTE_LEAF_ATTR_LO_S2_SH          GENMASK(9, 8)
// #define KVM_PTE_LEAF_ATTR_LO_S2_SH_IS       3
// #define KVM_PTE_LEAF_ATTR_LO_S2_AF          BIT(10)
#define KVM_PTE_LEAF_ATTR_HI                GENMASK(63, 51)
#define KVM_PTE_LEAF_ATTR_HI_S1_XN          BIT(54)
// #define KVM_PTE_LEAF_ATTR_HI_S2_XN          BIT(54)

/*INTERNAL*/ /* [[rc::parameters("pte : Pte")]] */
/*INTERNAL*/ /* [[rc::args("pte @ bitfield<Pte>")]] */
/*INTERNAL*/ /* [[rc::requires("{bitfield_wf pte}")]] */
/*INTERNAL*/ /* [[rc::returns("{pte_valid pte} @ builtin_boolean")]] */
bool kvm_pte_valid(kvm_pte_t pte)
{
    // TODO: remove 0 != once issue #45 is fixed
    return 0 != (pte & KVM_PTE_VALID);
}

/* [[rc::parameters("pte : Pte", "level : Z")]] */
/* [[rc::args("pte @ bitfield<Pte>", "level @ int<u32>")]] */
/* [[rc::requires("{bitfield_wf pte}")]] */
/* [[rc::returns("{if bool_decide (level = max_level - 1) then false \
    else if negb (pte_valid pte) then false \
    else bool_decide (pte_type pte = pte_type_table)} @ builtin_boolean")]] */
static bool kvm_pte_table(kvm_pte_t pte, u32 level)
{
    if (level == KVM_PGTABLE_MAX_LEVELS - 1)
        return false;
    if (!kvm_pte_valid(pte))
        return false;
    return FIELD_GET(KVM_PTE_TYPE, pte) == KVM_PTE_TYPE_TABLE;
}

/* [[rc::parameters("pte : Pte", "p : loc")]] */
/* [[rc::args("p @ &own<pte @ bitfield<Pte>>")]] */
/* [[rc::requires("{bitfield_wf pte}")]] */
/* [[rc::ensures("own p : {pte <| pte_valid := false |>} @ bitfield<Pte>")]] */
static void kvm_set_invalid_pte(kvm_pte_t *ptep)
{
    kvm_pte_t pte = *ptep;
    WRITE_ONCE(*ptep, pte & ~KVM_PTE_VALID);
}

/*INTERNAL*/ /* [[rc::parameters("pa : Z")]] */
/*INTERNAL*/ /* [[rc::args("pa @ int<u64>")]] */
/*INTERNAL*/ /* [[rc::returns("{mk_pte_addr (addr_of pa)} @ bitfield<Pte>")]] */
kvm_pte_t kvm_phys_to_pte(u64 pa)
{
    kvm_pte_t pte = pa & KVM_PTE_ADDR_MASK;

    if (PAGE_SHIFT == 16) // always false given PAGE_SHIFT == 12
        pte |= FIELD_PREP(KVM_PTE_ADDR_51_48, pa >> 48);

    return pte;
}

/*SPEC*/ /* [[rc::parameters("p : loc", "q : loc", "o : loc", "pte : Pte", "va : Z", "mm_ops : mm_callbacks")]] */
/*SPEC*/ /* [[rc::args("p @ &own<pte @ bitfield<Pte>>", "q @ &own<va @ int<u64>>",
           "o @ &own<mm_ops @ kvm_pgtable_mm_ops>")]] *//*SPEC*/ 
/*SPEC*/ /* [[rc::requires("{bitfield_wf pte}", "{pte_valid pte}")]] */
/*SPEC*/ /* [[rc::exists("pa : Z")]] */
/*SPEC*/ /* [[rc::ensures("{mm_ops.(virt_to_phys) va = pa}")]] */
/*SPEC*/ /* [[rc::ensures("own p : {mk_pte_addr (addr_of pa) <| pte_type := pte_type_table |>"
  "<| pte_valid := true |>} @ bitfield<Pte>")]] *//*SPEC*/ 
void kvm_set_table_pte(kvm_pte_t *ptep, kvm_pte_t *childp,
                  struct kvm_pgtable_mm_ops *mm_ops)
{
    kvm_pte_t old = *ptep, pte = kvm_phys_to_pte(mm_ops->virt_to_phys(childp));
    pte |= FIELD_PREP(KVM_PTE_TYPE, KVM_PTE_TYPE_TABLE);
    pte |= KVM_PTE_VALID;
    WARN_ON(kvm_pte_valid(old));
    // smp_store_release(ptep, pte);
    *ptep = pte;
}

/*SPEC*/ /* [[rc::parameters("p : loc", "pte : Pte", "pa : Z", "attr : Pte", "level : Z", "type : Z", "pte1 : Pte")]] */
/*SPEC*/ /* [[rc::args("p @ &own<pte @ bitfield<Pte>>", "pa @ int<u64>", "attr @ bitfield<Pte>", "level @ int<u32>")]] */
/*SPEC*/ /* [[rc::requires("{bitfield_wf pte}", "{bitfield_wf attr}")]] */
/*SPEC*/ /* [[rc::requires("{type = (if bool_decide (level = max_level - 1) then pte_type_page else pte_type_block)}")]] */
/*SPEC*/ /* [[rc::requires("{pte1 = mk_pte_addr (addr_of pa) <| pte_valid := true |> <| pte_type := type |>"
  "<| pte_leaf_attr_lo := pte_leaf_attr_lo attr |> <| pte_leaf_attr_hi := pte_leaf_attr_hi attr |>}")]] *//*SPEC*/ 
/*SPEC*/ /* [[rc::returns("{if pte_valid pte then bool_decide (bitfield_repr pte = bitfield_repr pte1) else true} @ builtin_boolean")]] */
/*SPEC*/ /* [[rc::ensures("own p : {if pte_valid pte then pte else pte1} @ bitfield<Pte>")]] */
bool kvm_set_valid_leaf_pte(kvm_pte_t *ptep, u64 pa, kvm_pte_t attr,
                   u32 level)
{
    kvm_pte_t old = *ptep, pte = kvm_phys_to_pte(pa);
    u64 type = (level == KVM_PGTABLE_MAX_LEVELS - 1) ? KVM_PTE_TYPE_PAGE :
                               KVM_PTE_TYPE_BLOCK;
    pte |= attr & (KVM_PTE_LEAF_ATTR_LO | KVM_PTE_LEAF_ATTR_HI);
    pte |= FIELD_PREP(KVM_PTE_TYPE, type);
    pte |= KVM_PTE_VALID;
    /* Tolerate KVM recreating the exact same mapping. */
    if (kvm_pte_valid(old))
        return old == pte;
    // smp_store_release(ptep, pte);
    *ptep = pte;
    return true;
}

struct /*PROOF*/ /* [[rc::refined_by("phys : Z", "attr : Attr", "mm_ops : mm_callbacks", "o : loc")]] */ hyp_map_data {
    /* [[rc::field("phys @ int<u64>")]] */
    u64                         phys;
    /* [[rc::field("attr @ bitfield<Attr>")]] */
    kvm_pte_t                   attr;
    /* [[rc::field("o @ &own<mm_ops @ kvm_pgtable_mm_ops>")]] */
    struct kvm_pgtable_mm_ops   *mm_ops;
};

/*SPEC*/ /* [[rc::parameters("prot : Prot", "phys : Z", "a : Attr", "attr : Attr",
                 "mtype : Z", "ap : Z", "xn : bool", "err : bool",//SPEC
                 "mm_ops : mm_callbacks", "o : loc", "d : loc")]] *///SPEC
/*SPEC*/ /* [[rc::args("prot @ bitfield<Prot>", "d @ &own<{(phys, a, mm_ops, o)} @ hyp_map_data>")]] */
/*SPEC*/ /* [[rc::requires("{bitfield_wf prot}")]] */
/*SPEC*/ /* [[rc::requires("{mtype = (if prot_device prot then mtype_device else mtype_normal)}")]] */
/*SPEC*/ /* [[rc::requires("{ap = (if prot_w prot then ap_rw else ap_ro)}")]] */
/*SPEC*/ /* [[rc::requires("{xn = negb (prot_x prot)}")]] */
/*SPEC*/ /* [[rc::requires("{err = negb (prot_r prot) || (prot_x prot && (prot_w prot || prot_device prot))}")]] */
/*SPEC*/ /* [[rc::requires("{attr = {| attr_lo_s1_attridx := mtype; attr_lo_s1_ap := ap; attr_lo_s1_sh := sh_is; attr_lo_s1_af := true; attr_hi_s1_xn := xn |} }")]] */
/*SPEC*/ /* [[rc::returns("{if err then -err_code else 0} @ int<i32>")]] */
/*SPEC*/ /* [[rc::ensures("own d : {if err then (phys, a, mm_ops, o) else (phys, attr, mm_ops, o)} @ hyp_map_data")]] */
int hyp_map_set_prot_attr(kvm_pgtable_prot prot, struct hyp_map_data *data)
{
    // TODO: remove 0 != once issue #45 is fixed
    bool device = 0 != (prot & KVM_PGTABLE_PROT_DEVICE);
    u32 mtype = device ? MT_DEVICE_nGnRE : MT_NORMAL;
    kvm_pte_t attr = FIELD_PREP(KVM_PTE_LEAF_ATTR_LO_S1_ATTRIDX, mtype);
    u32 sh = KVM_PTE_LEAF_ATTR_LO_S1_SH_IS;
    u32 ap = (prot & KVM_PGTABLE_PROT_W) ? KVM_PTE_LEAF_ATTR_LO_S1_AP_RW :
                           KVM_PTE_LEAF_ATTR_LO_S1_AP_RO;
    if (!(prot & KVM_PGTABLE_PROT_R))
        return -EINVAL;
    if (prot & KVM_PGTABLE_PROT_X) {
        if (prot & KVM_PGTABLE_PROT_W)
            return -EINVAL;
        if (device)
            return -EINVAL;
    } else {
        attr |= KVM_PTE_LEAF_ATTR_HI_S1_XN;
    }
    attr |= FIELD_PREP(KVM_PTE_LEAF_ATTR_LO_S1_AP, ap);
    attr |= FIELD_PREP(KVM_PTE_LEAF_ATTR_LO_S1_SH, sh);
    attr |= KVM_PTE_LEAF_ATTR_LO_S1_AF;
    data->attr = attr;
    return 0;
}
