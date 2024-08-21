/*GLOBAL*/ /*@ predicate kvm_pgtable_mm_ops(struct kvm_pgtable_mm_ops *p;) =
/*GLOBAL*/       kvm_pgtable_mm_ops_zalloc_page(p, _) &*&
/*GLOBAL*/       kvm_pgtable_mm_ops_zalloc_pages_exact(p, _) &*&
/*GLOBAL*/       kvm_pgtable_mm_ops_free_pages_exact(p, _) &*&
/*GLOBAL*/       kvm_pgtable_mm_ops_get_page(p, _) &*&
/*GLOBAL*/       kvm_pgtable_mm_ops_put_page(p, _) &*&
/*GLOBAL*/       kvm_pgtable_mm_ops_page_count(p, _) &*&
/*GLOBAL*/       kvm_pgtable_mm_ops_phys_to_virt(p, _) &*&
/*GLOBAL*/       kvm_pgtable_mm_ops_virt_to_phys(p, _);
/*GLOBAL*/ /*SYNTAX*/ @*/             

/*GLOBAL*/ /*@ predicate earlyAlloc(char* cur_val, unsigned long end_val) =
/*GLOBAL*/        chars((char*) cur_val, end_val-(unsigned long) cur_val, _) &*& (unsigned long) cur_val <= end_val; @*/

/*SPECS*/ /*@ predicate characters_zeroed(char* to, int count;) =
/*SPECS*/        count == 0 ? true : character(to, 0) &*& characters_zeroed(to + 1, count - 1); @*/
