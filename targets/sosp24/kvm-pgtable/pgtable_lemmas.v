From refinedc.typing Require Import typing.

(* pte *)

/*SPEC*/ Record Pte := mk_pte {
/*SPEC*/   pte_valid : bool;
/*SPEC*/   pte_type : Z;
/*SPEC*/   pte_leaf_attr_lo : Z;
/*SPEC*/   pte_addr : Z;
/*SPEC*/   pte_undef : Z;
/*SPEC*/   pte_leaf_attr_hi : Z;
/*SPEC*/ }.

/*SPEC*/ Global Instance Pte_settable : Settable _ := settable! mk_pte
/*SPEC*/   <pte_valid; pte_type; pte_leaf_attr_lo; pte_addr; pte_undef; pte_leaf_attr_hi>.

/*SPEC*/ Definition empty_pte := {|
/*SPEC*/   pte_valid := false;
/*SPEC*/   pte_type := 0;
/*SPEC*/   pte_leaf_attr_lo := 0;
/*SPEC*/   pte_addr := 0;
/*SPEC*/   pte_undef := 0;
/*SPEC*/   pte_leaf_attr_hi := 0;
/*SPEC*/ /*SYNTAX*/ |}.

/*SPEC*/ Definition mk_pte_addr (a : addr) : Pte := empty_pte <| pte_addr := a |>.

/*SPEC*/ Definition pte_repr (p : Pte) : Z :=
/*SPEC*/   bf_cons 0 1 (bool_to_Z $ pte_valid p) $
/*SPEC*/   bf_cons 1 1 (pte_type p) $
/*SPEC*/   bf_cons 2 10 (pte_leaf_attr_lo p) $
/*SPEC*/   bf_cons 12 36 (pte_addr p) $
/*SPEC*/   bf_cons 48 3 (pte_undef p) $
/*SPEC*/   bf_cons 51 13 (pte_leaf_attr_hi p) $
/*SPEC*/   bf_nil.

/*PROOF CONTROL*/ Arguments pte_repr _/.

/*SPEC*/ Definition pte_wf (p : Pte) : Prop :=
/*SPEC*/   0 ≤ bool_to_Z $ pte_valid p < 2^1 ∧
/*SPEC*/   0 ≤ pte_type p < 2^1 ∧
/*SPEC*/   0 ≤ pte_leaf_attr_lo p < 2^10 ∧
/*SPEC*/   0 ≤ pte_addr p < 2^36 ∧
/*SPEC*/   0 ≤ pte_undef p < 2^3 ∧
/*SPEC*/   0 ≤ pte_leaf_attr_hi p < 2^13.
/*PROOF CONTROL*/ Global Typeclasses Opaque pte_wf.

/*PROOF CONTROL*/ Global Instance simpl_pte_wf_impl p :
/*PROOF CONTROL*/   SimplImpl (pte_wf p) ltac:(let x := eval unfold pte_wf in (pte_wf p) in exact x).
/*PROOF*/ Proof. done. Qed.

/*SPEC*/ Global Instance Pte_BitfieldDesc : BitfieldDesc Pte := {|
/*SPEC*/   bitfield_it := u64;
/*SPEC*/   bitfield_repr := pte_repr;
/*SPEC*/   bitfield_wf := pte_wf;
/*SPEC*/ /*SYNTAX*/ |}.

/*PROOF CONTROL*/ Global Instance simpl_exist_Pte Σ : @SimplExist Σ Pte
/*PROOF CONTROL*/   (λ P, ∃ valid type leaf_attr_lo addr undef leaf_attr_hi,
/*PROOF CONTROL*/     P {|
/*PROOF CONTROL*/       pte_valid := valid;
/*PROOF CONTROL*/       pte_type := type;
/*PROOF CONTROL*/       pte_leaf_attr_lo := leaf_attr_lo;
/*PROOF CONTROL*/       pte_addr := addr;
/*PROOF CONTROL*/       pte_undef := undef;
/*PROOF CONTROL*/       pte_leaf_attr_hi := leaf_attr_hi;
/*PROOF CONTROL*/ /*SYNTAX*/     |})%I.
/*PROOF*/ Proof. iIntros (?) "(%&%&%&%&%&%&?)". by iExists _. Qed.
/*PROOF CONTROL*/ Global Instance simpl_forall_Pte P : SimplForall Pte 6 P
/*PROOF CONTROL*/   (∀ valid type leaf_attr_lo addr undef leaf_attr_hi,
/*PROOF CONTROL*/     P {|
/*PROOF CONTROL*/       pte_valid := valid;
/*PROOF CONTROL*/       pte_type := type;
/*PROOF CONTROL*/       pte_leaf_attr_lo := leaf_attr_lo;
/*PROOF CONTROL*/       pte_addr := addr;
/*PROOF CONTROL*/       pte_undef := undef;
/*PROOF CONTROL*/       pte_leaf_attr_hi := leaf_attr_hi;
/*PROOF CONTROL*/ /*SYNTAX*/     |}).
/*PROOF*/ Proof. unfold SimplForall => ? []. naive_solver. Qed.

/*SPEC*/ Definition addr_of (n : Z) : Z :=
/*SPEC*/   bf_slice 12 36 n.

(* pte attr *)

/*SPEC*/ Record Attr := {
/*SPEC*/   attr_lo_s1_attridx : Z;
/*SPEC*/   attr_lo_s1_ap : Z;
/*SPEC*/   attr_lo_s1_sh : Z;
/*SPEC*/   attr_lo_s1_af : bool;
/*SPEC*/   attr_hi_s1_xn : bool;
/*SPEC*/ /*SYNTAX*/ }.

/*SPEC*/ Definition attr_repr (a : Attr) : Z :=
/*SPEC*/   bf_cons 2 2 (attr_lo_s1_attridx a) $
/*SPEC*/   bf_cons 6 2 (attr_lo_s1_ap a) $
/*SPEC*/   bf_cons 8 2 (attr_lo_s1_sh a) $
/*SPEC*/   bf_cons 10 1 (bool_to_Z $ attr_lo_s1_af a) $
/*SPEC*/   bf_cons 54 1 (bool_to_Z $ attr_hi_s1_xn a)
/*SPEC*/   bf_nil.

/*PROOF CONTROL*/ Arguments attr_repr _/.

/*SPEC*/ Definition attr_wf (a : Attr) : Prop :=
/*SPEC*/   0 ≤ attr_lo_s1_attridx a < 2^2 ∧
/*SPEC*/   0 ≤ attr_lo_s1_ap a < 2^2 ∧
/*SPEC*/   0 ≤ attr_lo_s1_sh a < 2^2 ∧
/*SPEC*/   0 ≤ bool_to_Z $ attr_lo_s1_af a < 2^1 ∧
/*SPEC*/   0 ≤ bool_to_Z $ attr_hi_s1_xn a < 2^1.
/*SPEC*/ Global Typeclasses Opaque attr_wf.

/*PROOF CONTROL*/ Global Instance simpl_attr_wf_impl a :
/*PROOF CONTROL*/   SimplImpl (attr_wf a) ltac:(let x := eval unfold attr_wf in (attr_wf a) in exact x).
/*PROOF*/ Proof. done. Qed.

/*SPEC*/ Global Instance Attr_BitfieldDesc : BitfieldDesc Attr := {|
/*SPEC*/   bitfield_it := u64;
/*SPEC*/   bitfield_repr := attr_repr;
/*SPEC*/   bitfield_wf := attr_wf;
/*SPEC*/ /*SYNTAX*/ |}.

(* pte prot *)

/*SPEC*/ Record Prot := {
/*SPEC*/   prot_x : bool;
/*SPEC*/   prot_w : bool;
/*SPEC*/   prot_r : bool;
/*SPEC*/   prot_device : bool;
/*SPEC*/ /*SYNTAX*/ }.

/*SPEC*/ Definition prot_repr (p : Prot) : Z :=
/*SPEC*/   bf_cons 0 1 (bool_to_Z $ prot_x p) $
/*SPEC*/   bf_cons 1 1 (bool_to_Z $ prot_w p) $
/*SPEC*/   bf_cons 2 1 (bool_to_Z $ prot_r p) $
/*SPEC*/   bf_cons 3 1 (bool_to_Z $ prot_device p) $
/*SPEC*/   bf_nil.

/*PROOF CONTROL*/ Arguments prot_repr _/.

/*SPEC*/ Definition prot_wf (p : Prot) : Prop :=
/*SPEC*/   0 ≤ bool_to_Z $ prot_x p < 2^1 ∧
/*SPEC*/   0 ≤ bool_to_Z $ prot_w p < 2^1 ∧
/*SPEC*/   0 ≤ bool_to_Z $ prot_r p < 2^1 ∧
/*SPEC*/   0 ≤ bool_to_Z $ prot_device p < 2^1.
/*SPEC*/ Global Typeclasses Opaque prot_wf.

/*PROOF CONTROL*/ Global Instance simpl_prot_wf_impl p :
/*PROOF CONTROL*/   SimplImpl (prot_wf p) ltac:(let x := eval unfold prot_wf in (prot_wf p) in exact x).
/*PROOF*/ Proof. done. Qed.

/*SPEC*/ Global Instance Prot_BitfieldDesc : BitfieldDesc Prot := {|
/*SPEC*/   bitfield_it := u64;
/*SPEC*/   bitfield_repr := prot_repr;
/*SPEC*/   bitfield_wf := prot_wf;
/*SPEC*/ /*SYNTAX*/ |}.
/*PROOF CONTROL*/ Global Instance simpl_exist_Prot Σ : @SimplExist Σ Prot (λ P, ∃ x w r device,
/*PROOF CONTROL*/   P {| prot_x := x; prot_w := w; prot_r := r; prot_device := device |})%I.
/*PROOF*/ Proof. iIntros (?) "(%&%&%&%&?)". by iExists _. Qed.
/*PROOF CONTROL*/ Global Instance simpl_forall_Prot P : SimplForall Prot 4 P (∀ x w r device,
/*PROOF CONTROL*/   P {| prot_x := x; prot_w := w; prot_r := r; prot_device := device |}).
/*PROOF*/ Proof. unfold SimplForall => ? []. naive_solver. Qed.

(* struct, const *)

/*SPEC*/ Record mm_callbacks := {
/*SPEC*/   virt_to_phys : Z → Z;
/*SPEC*/ /*SYNTAX*/ }.

/*SPEC*/ Definition max_level : Z := 4.
/*SPEC*/ Definition mtype_device : Z := 5.
/*SPEC*/ Definition mtype_normal : Z := 0.
/*SPEC*/ Definition pte_type_block : Z := 0.
/*SPEC*/ Definition pte_type_page : Z := 1.
/*SPEC*/ Definition pte_type_table : Z := 1.
/*SPEC*/ Definition ap_rw : Z := 1.
/*SPEC*/ Definition ap_ro : Z := 3.
/*SPEC*/ Definition sh_is : Z := 3.
/*SPEC*/ Definition err_code : Z := 22.
