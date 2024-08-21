#include <tpot_primitives.h>
#include "defs.h"

/*SPECS*/void spec__kvm_set_table_pte() {
/*SPECS*/    any(kvm_pte_t *, ptep); any(kvm_pte_t *, child_ptep); any(struct kvm_pgtable_mm_ops *, mm_ops);
/*SPECS*/    assume(names_obj(ptep, kvm_pte_t));
/*SPECS*/    assume(names_obj(child_ptep, kvm_pte_t));
/*SPECS*/    assume(names_obj(mm_ops, struct kvm_pgtable_mm_ops));

/*SPECS*/    mm_ops->virt_to_phys = &uninterp__virt_to_phys;

             // old should not be valid. Not sure why this isn't in the RefinedC spec.
/*SPECS*/    assume(!kvm_pte_valid(*ptep));

/*SPECS*/    kvm_set_table_pte(ptep, child_ptep, mm_ops);

/*SPECS*/    kvm_pte_t expected = kvm_phys_to_pte(uninterp__virt_to_phys(child_ptep)) 
/*SPECS*/        | KVM_PTE_VALID | FIELD_PREP(KVM_PTE_TYPE, KVM_PTE_TYPE_TABLE);
/*SPECS*/    assert(*ptep == expected);

/*SPECS*/    assert(names_obj(ptep, kvm_pte_t));
 /*SPECS*/    assert(names_obj(child_ptep, kvm_pte_t));
/*SPECS*/    assert(names_obj(mm_ops, struct kvm_pgtable_mm_ops));
/*SPECS*/} /*SYNTAX*/

/*SPECS*/void spec__kvm_set_valid_leaf_pte() {
/*SPECS*/    any(kvm_pte_t *, ptep); any(u64, pa); any(kvm_pte_t, attr); any(u32, level);

/*SPECS*/    assume(names_obj(ptep, kvm_pte_t));
/*SPECS*/    kvm_pte_t old_pte = *ptep;

/*SPECS*/    bool res = kvm_set_valid_leaf_pte(ptep, pa, attr, level);

/*SPECS*/    kvm_pte_t type = level == KVM_PGTABLE_MAX_LEVELS - 1 ? KVM_PTE_TYPE_PAGE : KVM_PTE_TYPE_BLOCK;
/*SPECS*/    kvm_pte_t expected_pte = kvm_phys_to_pte(pa) 
/*SPECS*/        | KVM_PTE_VALID | FIELD_PREP(KVM_PTE_TYPE, type)
/*SPECS*/        | attr & (KVM_PTE_LEAF_ATTR_LO | KVM_PTE_LEAF_ATTR_HI);

/*SPECS*/    if (kvm_pte_valid(old_pte)) {
/*SPECS*/        assert(res == (*ptep == expected_pte));
/*SPECS*/        assert(*ptep == old_pte);
/*SPECS*/    } else {
/*SPECS*/        assert(res);
/*SPECS*/        assert(*ptep == expected_pte);
/*SPECS*/    } /*SYNTAX*/
/*SPECS*/    assert(names_obj(ptep, kvm_pte_t));
/*SPECS*/} /*SYNTAX*/

/*SPECS*/void spec__hyp_map_set_prot_attr() {
/*SPECS*/  any(kvm_pgtable_prot, prot); any(struct hyp_map_data *, data);
/*SPECS*/  assume(names_obj(data, struct hyp_map_data));
/*SPECS*/
/*SPECS*/  bool err_cond = !(prot & KVM_PGTABLE_PROT_R) ||
/*SPECS*/                  (prot & KVM_PGTABLE_PROT_X && 
/*SPECS*/                    (prot & KVM_PGTABLE_PROT_W ||
/*SPECS*/                     prot & KVM_PGTABLE_PROT_DEVICE));

/*SPECS*/  struct hyp_map_data old_data = *data;
/*SPECS*/
/*SPECS*/  int res = hyp_map_set_prot_attr(prot, data);
/*SPECS*/  if (err_cond) {
/*SPECS*/    assert(res == -EINVAL);
/*SPECS*/    assert(data->phys == old_data.phys);
/*SPECS*/    assert(data->attr == old_data.attr);
/*SPECS*/    assert(data->mm_ops == old_data.mm_ops);
/*SPECS*/  } else {
/*SPECS*/    assert(res == 0);

/*SPECS*/    struct hyp_map_data expected = old_data;
/*SPECS*/    bool device = prot & KVM_PGTABLE_PROT_DEVICE;
/*SPECS*/    kvm_pte_t expected_attr = FIELD_PREP(KVM_PTE_LEAF_ATTR_LO_S1_ATTRIDX,
/*SPECS*/                            device ? MT_DEVICE_nGnRE : MT_NORMAL);
/*SPECS*/    u32 ap = (prot & KVM_PGTABLE_PROT_W) ? KVM_PTE_LEAF_ATTR_LO_S1_AP_RW :
/*SPECS*/                           KVM_PTE_LEAF_ATTR_LO_S1_AP_RO;
/*SPECS*/    expected_attr |= FIELD_PREP(KVM_PTE_LEAF_ATTR_LO_S1_AP, ap);
/*SPECS*/    expected_attr |= FIELD_PREP(KVM_PTE_LEAF_ATTR_LO_S1_SH, KVM_PTE_LEAF_ATTR_LO_S1_SH_IS);
/*SPECS*/    expected_attr |= KVM_PTE_LEAF_ATTR_LO_S1_AF;
/*SPECS*/    if (!(prot & KVM_PGTABLE_PROT_X)) {
/*SPECS*/      expected_attr |= KVM_PTE_LEAF_ATTR_HI_S1_XN;
/*SPECS*/    } /*SYNTAX*/

/*SPECS*/    assert(data->phys == old_data.phys);
/*SPECS*/    assert(data->attr == expected_attr);
/*SPECS*/    assert(data->mm_ops == old_data.mm_ops);
/*SPECS*/  } /*SYNTAX*/
/*SPECS*/  assert(names_obj(data, struct hyp_map_data));
/*SPECS*/} /*SYNTAX*/