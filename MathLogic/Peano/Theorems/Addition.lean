import MathLogic.Peano.Deduction

namespace Peano

variable {α : Type} [BEq α] [LawfulBEq α]
variable [ClassicalFOLDeduction PeanoSignature α]
variable [EqualityDeduction PeanoSignature α PeanoPred.eq]
variable [PeanoDeduction α]

theorem zero_add (x : α) [PeanoEquality α] : ⊢ (0 + V x) ≃ V x := by
  let p : Formula PeanoSignature α := (0 + V x) ≃ V x

  let h_base : ⊢ p⟦x := 0⟧ := by
    have h_subst : p⟦x := 0⟧ = ((0 + 0) ≃ 0) := by
      simp only [peanoEq, HAdd.hAdd, Add.add, OfNat.ofNat, V, substF, List.map_cons, substT,
        List.map_nil, BEq.rfl, ↓reduceIte, p]
    rw [h_subst]
    exact PeanoDeduction.add_zero 0

  let h_step_imp : ⊢ p ⇒ p⟦x := S' (V x)⟧ := by
    have h_subst : p⟦x := S' (V x)⟧ = ((0 + S' (V x)) ≃ S' (V x)) := by
      simp only [peanoEq, HAdd.hAdd, Add.add, OfNat.ofNat, V, substF, List.map_cons, substT,
        List.map_nil, BEq.rfl, ↓reduceIte, p]
    rw [h_subst]
    apply MinimalFOLDeduction.deduction
    intro h_ih
    let h1 := PeanoDeduction.add_succ 0 (V x)
    let h2_imp := PeanoEquality.cong_succ (0 + V x) (V x)
    let h2 := MinimalFOLDeduction.mp h2_imp h_ih
    let h3_imp := EqualityDeduction.trans (0 + S' (V x)) (S' (0 + V x)) (S' (V x))
    let h3_part1 := MinimalFOLDeduction.mp h3_imp h1
    exact MinimalFOLDeduction.mp h3_part1 h2

  let h_step : ⊢ ∀' x, p ⇒ p⟦x := S' (V x)⟧ := rule_gen_simple x h_step_imp

  let h_ind_schema := PeanoDeduction.induction p x
  let h_all := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_ind_schema h_base) h_step

  exact forall_elim_simple x h_all

theorem succ_add (x y : α) (h_neq : (y == x) = false) [PeanoEquality α] : ⊢ (S' (V x) + V y) ≃ S' (V x + V y) := by
  let p : Formula PeanoSignature α := (S' (V x) + V y) ≃ S' (V x + V y)

  let h_base : ⊢ p⟦y := 0⟧ := by
    have h_subst : p⟦y := 0⟧ = ((S' (V x) + 0) ≃ S' (V x + 0)) := by
      unfold p substF
      simp (config := { decide := true }) only [peanoEq, HAdd.hAdd, Add.add, succ, V, List.map,
        OfNat.ofNat, substT, h_neq, Bool.false_eq_true, ↓reduceIte, BEq.rfl]
    rw [h_subst]
    let h1 := PeanoDeduction.add_zero (S' (V x))
    let h2 := PeanoDeduction.add_zero (V x)
    let h3_imp := PeanoEquality.cong_succ (V x + 0) (V x)
    let h3 := MinimalFOLDeduction.mp h3_imp h2
    let h4_imp := EqualityDeduction.symm (S' (V x + 0)) (S' (V x))
    let h4 := MinimalFOLDeduction.mp h4_imp h3
    let h5_imp := EqualityDeduction.trans (S' (V x) + 0) (S' (V x)) (S' (V x + 0))
    let h5 := MinimalFOLDeduction.mp h5_imp h1
    exact MinimalFOLDeduction.mp h5 h4

  let h_step_imp : ⊢ p ⇒ p⟦y := S' (V y)⟧ := by
    have h_subst : p⟦y := S' (V y)⟧ = ((S' (V x) + S' (V y)) ≃ S' (V x + S' (V y))) := by
      unfold p substF
      simp (config := { decide := true }) only [peanoEq, HAdd.hAdd, Add.add, succ, V, List.map,
        substT, h_neq, Bool.false_eq_true, ↓reduceIte, BEq.rfl]
    rw [h_subst]
    apply MinimalFOLDeduction.deduction
    intro h_ih
    let h1 := PeanoDeduction.add_succ (S' (V x)) (V y)
    let h2_imp := PeanoEquality.cong_succ (S' (V x) + V y) (S' (V x + V y))
    let h2 := MinimalFOLDeduction.mp h2_imp h_ih
    let t1_imp := EqualityDeduction.trans (S' (V x) + S' (V y)) (S' (S' (V x) + V y)) (S' (S' (V x + V y)))
    let t1_part := MinimalFOLDeduction.mp t1_imp h1
    let h_1_2 := MinimalFOLDeduction.mp t1_part h2
    let h3 := PeanoDeduction.add_succ (V x) (V y)
    let h4_imp := PeanoEquality.cong_succ (V x + S' (V y)) (S' (V x + V y))
    let h4 := MinimalFOLDeduction.mp h4_imp h3
    let sym_imp := EqualityDeduction.symm (S' (V x + S' (V y))) (S' (S' (V x + V y)))
    let h5 := MinimalFOLDeduction.mp sym_imp h4
    let t2_imp := EqualityDeduction.trans (S' (V x) + S' (V y)) (S' (S' (V x + V y))) (S' (V x + S' (V y)))
    let t2_part := MinimalFOLDeduction.mp t2_imp h_1_2
    exact MinimalFOLDeduction.mp t2_part h5

  let h_step : ⊢ ∀' y, p ⇒ p⟦y := S' (V y)⟧ := rule_gen_simple y h_step_imp

  let h_ind_schema := PeanoDeduction.induction p y
  let h_all := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_ind_schema h_base) h_step

  exact forall_elim_simple y h_all

theorem add_assoc (x y z : α) (h_zx : (z == x) = false) (h_zy : (z == y) = false) [PeanoEquality α] : ⊢ ((V x + V y) + V z) ≃ (V x + (V y + V z)) := by
  let p : Formula PeanoSignature α := ((V x + V y) + V z) ≃ (V x + (V y + V z))

  let h_base : ⊢ p⟦z := 0⟧ := by
    have h_subst : p⟦z := 0⟧ = (((V x + V y) + 0) ≃ (V x + (V y + 0))) := by
      unfold p substF
      simp (config := { decide := true }) only [peanoEq, HAdd.hAdd, Add.add, V, List.map,
        OfNat.ofNat, substT, h_zx, Bool.false_eq_true, ↓reduceIte, h_zy, BEq.rfl]
    rw [h_subst]
    let h1 := PeanoDeduction.add_zero (V x + V y)
    let h2 := PeanoDeduction.add_zero (V y)
    let h3_refl := EqualityDeduction.refl (V x)
    let h4_imp := PeanoEquality.cong_add (V x) (V x) (V y + 0) (V y)
    let h4 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h4_imp h3_refl) h2
    let h4_symm := MinimalFOLDeduction.mp (EqualityDeduction.symm (V x + (V y + 0)) (V x + V y)) h4
    let h_trans := EqualityDeduction.trans ((V x + V y) + 0) (V x + V y) (V x + (V y + 0))
    let h_mid := MinimalFOLDeduction.mp h_trans h1
    exact MinimalFOLDeduction.mp h_mid h4_symm

  let h_step_imp : ⊢ p ⇒ p⟦z := S' (V z)⟧ := by
    have h_subst : p⟦z := S' (V z)⟧ = (((V x + V y) + S' (V z)) ≃ (V x + (V y + S' (V z)))) := by
      unfold p substF
      simp (config := { decide := true }) only [peanoEq, HAdd.hAdd, Add.add, V, List.map, succ,
        substT, h_zx, Bool.false_eq_true, ↓reduceIte, h_zy, BEq.rfl]
    rw [h_subst]
    apply MinimalFOLDeduction.deduction
    intro h_ih
    let h1 := PeanoDeduction.add_succ (V x + V y) (V z)
    let h2 := MinimalFOLDeduction.mp (PeanoEquality.cong_succ ((V x + V y) + V z) (V x + (V y + V z))) h_ih
    let h3 := PeanoDeduction.add_succ (V y) (V z)
    let h4_refl := EqualityDeduction.refl (V x)
    let h5_imp := PeanoEquality.cong_add (V x) (V x) (V y + S' (V z)) (S' (V y + V z))
    let h5 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h5_imp h4_refl) h3
    let h6 := PeanoDeduction.add_succ (V x) (V y + V z)
    let h7_trans := EqualityDeduction.trans (V x + (V y + S' (V z))) (V x + S' (V y + V z)) (S' (V x + (V y + V z)))
    let h7 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h7_trans h5) h6
    let h7_symm := MinimalFOLDeduction.mp (EqualityDeduction.symm (V x + (V y + S' (V z))) (S' (V x + (V y + V z)))) h7
    let h8_trans := EqualityDeduction.trans ((V x + V y) + S' (V z)) (S' ((V x + V y) + V z)) (S' (V x + (V y + V z)))
    let h8 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h8_trans h1) h2
    let h_final_trans := EqualityDeduction.trans ((V x + V y) + S' (V z)) (S' (V x + (V y + V z))) (V x + (V y + S' (V z)))
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_final_trans h8) h7_symm

  let h_step : ⊢ ∀' z, p ⇒ p⟦z := S' (V z)⟧ := rule_gen_simple z h_step_imp
  let h_ind_schema := PeanoDeduction.induction p z
  let h_all := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_ind_schema h_base) h_step
  exact forall_elim_simple z h_all

theorem add_comm (x y : α) (h_yx : (y == x) = false) [PeanoEquality α] : ⊢ (V x + V y) ≃ (V y + V x) := by
  let p : Formula PeanoSignature α := (V x + V y) ≃ (V y + V x)

  let h_base : ⊢ p⟦y := 0⟧ := by
    have h_subst : p⟦y := 0⟧ = (V x + 0 ≃ 0 + V x) := by
      unfold p substF
      simp (config := { decide := true }) only [peanoEq, HAdd.hAdd, Add.add, V, List.map,
        OfNat.ofNat, substT, h_yx, Bool.false_eq_true, ↓reduceIte, BEq.rfl]
    rw [h_subst]
    let h1 := PeanoDeduction.add_zero (V x)
    let h2 := zero_add x
    let h2_symm := MinimalFOLDeduction.mp (EqualityDeduction.symm (0 + V x) (V x)) h2
    let h_trans := EqualityDeduction.trans (V x + 0) (V x) (0 + V x)
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_trans h1) h2_symm

  let h_step_imp : ⊢ p ⇒ p⟦y := S' (V y)⟧ := by
    have h_subst : p⟦y := S' (V y)⟧ = (V x + S' (V y) ≃ S' (V y) + V x) := by
      unfold p substF
      simp (config := { decide := true }) only [peanoEq, HAdd.hAdd, Add.add, V, List.map, succ,
        substT, h_yx, Bool.false_eq_true, ↓reduceIte, BEq.rfl]
    rw [h_subst]
    apply MinimalFOLDeduction.deduction
    intro h_ih
    let h1 := PeanoDeduction.add_succ (V x) (V y)
    let h2 := MinimalFOLDeduction.mp (PeanoEquality.cong_succ (V x + V y) (V y + V x)) h_ih
    let h_xy_neq : (x == y) = false := by
      rw [BEq.comm]
      exact h_yx
    let h3 := succ_add y x h_xy_neq
    let h3_symm := MinimalFOLDeduction.mp (EqualityDeduction.symm (S' (V y) + V x) (S' (V y + V x))) h3
    let h_trans_lhs := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans (V x + S' (V y)) (S' (V x + V y)) (S' (V y + V x))) h1) h2
    let h_trans_final := EqualityDeduction.trans (V x + S' (V y)) (S' (V y + V x)) (S' (V y) + V x)
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_trans_final h_trans_lhs) h3_symm

  let h_step : ⊢ ∀' y, p ⇒ p⟦y := S' (V y)⟧ := rule_gen_simple y h_step_imp
  let h_ind_schema := PeanoDeduction.induction p y
  let h_all := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_ind_schema h_base) h_step
  exact forall_elim_simple y h_all

theorem add_right_cancel (x y z : α) (h_zx : (z == x) = false) (h_zy : (z == y) = false) : ⊢ ((V x + V z) ≃ (V y + V z)) ⇒ (V x ≃ V y) := by
  let p : Formula PeanoSignature α := ((V x + V z) ≃ (V y + V z)) ⇒ (V x ≃ V y)

  let h_base : ⊢ p⟦z := 0⟧ := by
    have h_subst : p⟦z := 0⟧ = ((V x + 0 ≃ V y + 0) ⇒ (V x ≃ V y)) := by
      unfold p
      simp (config := { decide := true }) only [substF, peanoEq, HAdd.hAdd, Add.add, V, OfNat.ofNat,
        List.map, substT, h_zx, Bool.false_eq_true, ↓reduceIte, BEq.rfl, h_zy]
    rw [h_subst]
    apply MinimalFOLDeduction.deduction
    intro h_hyp
    let h_x0 := PeanoDeduction.add_zero (V x)
    let h_y0 := PeanoDeduction.add_zero (V y)
    let h1 := MinimalFOLDeduction.mp (EqualityDeduction.symm (V x + 0) (V x)) h_x0
    let h2 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans (V x) (V x + 0) (V y + 0)) h1) h_hyp
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans (V x) (V y + 0) (V y)) h2) h_y0

  let h_step_imp : ⊢ p ⇒ p⟦z := S' (V z)⟧ := by
    have h_subst : p⟦z := S' (V z)⟧ = ((V x + S' (V z) ≃ V y + S' (V z)) ⇒ (V x ≃ V y)) := by
      unfold p
      simp (config := { decide := true }) only [substF, peanoEq, HAdd.hAdd, Add.add, V, List.map,
        substT, h_zx, Bool.false_eq_true, ↓reduceIte, BEq.rfl, h_zy]
    rw [h_subst]
    apply MinimalFOLDeduction.deduction
    intro h_ih
    apply MinimalFOLDeduction.deduction
    intro h_hyp_succ
    let h_add_sx := PeanoDeduction.add_succ (V x) (V z)
    let h_add_sy := PeanoDeduction.add_succ (V y) (V z)
    let h_symm_sx := MinimalFOLDeduction.mp (EqualityDeduction.symm (V x + S' (V z)) (S' (V x + V z))) h_add_sx
    let h_trans1_imp := MinimalFOLDeduction.mp (EqualityDeduction.trans (S' (V x + V z)) (V x + S' (V z)) (V y + S' (V z))) h_symm_sx
    let h_trans1 := MinimalFOLDeduction.mp h_trans1_imp h_hyp_succ
    let h_s_eq_imp := MinimalFOLDeduction.mp (EqualityDeduction.trans (S' (V x + V z)) (V y + S' (V z)) (S' (V y + V z))) h_trans1
    let h_s_eq := MinimalFOLDeduction.mp h_s_eq_imp h_add_sy
    let h_inj := PeanoDeduction.succ_inj (V x + V z) (V y + V z)
    let h_xz_eq_yz := MinimalFOLDeduction.mp h_inj h_s_eq
    exact MinimalFOLDeduction.mp h_ih h_xz_eq_yz

  let h_step : ⊢ ∀' z, p ⇒ p⟦z := S' (V z)⟧ := rule_gen_simple z h_step_imp
  let h_all := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoDeduction.induction p z) h_base) h_step
  exact forall_elim_simple z h_all

end Peano
