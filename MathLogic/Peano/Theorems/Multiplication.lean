import MathLogic.Peano.Deduction
import MathLogic.Peano.Theorems.Addition

namespace Peano

variable {α : Type} [BEq α] [LawfulBEq α]
variable [ClassicalFOLDeduction PeanoSignature α]
variable [EqualityDeduction PeanoSignature α PeanoPred.eq]
variable [PeanoDeduction α]

theorem zero_mul (x : α) [PeanoEquality α] : ⊢ (0 * V x) ≃ 0 := by
  let p : Formula PeanoSignature α := (0 * V x) ≃ 0

  let h_base : ⊢ p⟦x := 0⟧ := by
    have h_subst : p⟦x := 0⟧ = (0 * 0 ≃ 0) := by
      unfold p substF
      simp only [HMul.hMul, Mul.mul, V, OfNat.ofNat, peanoEq]
      unfold substT
      simp only [List.map, substT, BEq.rfl, ↓reduceIte]
    rw [h_subst]
    exact PeanoDeduction.mul_zero 0

  let h_step_imp : ⊢ p ⇒ p⟦x := S' (V x)⟧ := by
    have h_subst : p⟦x := S' (V x)⟧ = (0 * S' (V x) ≃ 0) := by
      unfold p substF
      simp only [HMul.hMul, Mul.mul, V, OfNat.ofNat, peanoEq]
      unfold substT
      simp only [List.map, substT, BEq.rfl, ↓reduceIte]
    rw [h_subst]
    apply MinimalFOLDeduction.deduction
    intro h_ih
    let h1 := PeanoDeduction.mul_succ 0 (V x)
    let h2 := PeanoDeduction.add_zero (0 * V x)
    let h3_trans := EqualityDeduction.trans (0 * S' (V x)) (0 * V x + 0) (0 * V x)
    let h3 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h3_trans h1) h2
    let h4_trans := EqualityDeduction.trans (0 * S' (V x)) (0 * V x) 0
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h4_trans h3) h_ih
  let h_step : ⊢ ∀' x, p ⇒ p⟦x := S' (V x)⟧ := rule_gen_simple x h_step_imp
  let h_ind_schema := PeanoDeduction.induction p x
  let h_all := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_ind_schema h_base) h_step
  exact forall_elim_simple x h_all

theorem succ_mul (x y : α) (h_neq : (y == x) = false) [PeanoEquality α] : ⊢ (S' (V x) * V y) ≃ ((V x * V y) + V y) := by
  let p : Formula PeanoSignature α := (S' (V x) * V y) ≃ ((V x * V y) + V y)
  have h_neq' : (x == y) = false := by
    rw [BEq.comm]
    exact h_neq

  let h_base : ⊢ p⟦x := 0⟧ := by
    have h_subst : p⟦x := 0⟧ = (S' (0) * V y ≃ ((0 * V y) + V y)) := by
      unfold p
      simp (config := { decide := true }) only [peanoEq, HMul.hMul, Mul.mul, succ, V, HAdd.hAdd,
        Add.add, OfNat.ofNat, substF, List.map, substT, BEq.rfl, ↓reduceIte, h_neq',
        Bool.false_eq_true]
    rw [h_subst]

    let q_one_mul : Formula PeanoSignature α := (S' 0 * V y) ≃ V y
    let q_om_base : ⊢ q_one_mul⟦y := 0⟧ := by
      unfold q_one_mul substF
      simp only [HMul.hMul, Mul.mul, V, succ, OfNat.ofNat, peanoEq]
      unfold substT
      simp only [List.map, substT, BEq.rfl, ↓reduceIte]
      exact PeanoDeduction.mul_zero (S' 0)
    let q_om_step : ⊢ ∀' y, q_one_mul ⇒ q_one_mul⟦y := S' (V y)⟧ := by
      apply rule_gen_simple
      apply MinimalFOLDeduction.deduction
      intro ih
      have h_sub : q_one_mul⟦y := S' (V y)⟧ = (S' 0 * S' (V y) ≃ S' (V y)) := by
        unfold q_one_mul substF
        simp only [HMul.hMul, Mul.mul, V, succ, OfNat.ofNat, peanoEq]
        unfold substT
        simp only [List.map, substT, BEq.rfl, ↓reduceIte]
      rw [h_sub]
      let h1 := PeanoDeduction.mul_succ (S' 0) (V y)
      let h2_imp := PeanoEquality.cong_add (S' 0 * V y) (V y) (S' 0) (S' 0)
      let h2 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h2_imp ih) (EqualityDeduction.refl (S' 0))
      let h3 := PeanoDeduction.add_succ (V y) 0
      let h4 := MinimalFOLDeduction.mp (PeanoEquality.cong_succ (V y + 0) (V y)) (PeanoDeduction.add_zero (V y))
      let h5_imp := EqualityDeduction.trans (V y + S' 0) (S' (V y + 0)) (S' (V y))
      let h5 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h5_imp h3) h4
      let h6_imp := EqualityDeduction.trans (S' 0 * S' (V y)) (S' 0 * V y + S' 0) (V y + S' 0)
      let h6 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h6_imp h1) h2
      let h_final_imp := EqualityDeduction.trans (S' 0 * S' (V y)) (V y + S' 0) (S' (V y))
      exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_final_imp h6) h5
    let h_one_mul := forall_elim_simple y (MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoDeduction.induction q_one_mul y) q_om_base) q_om_step)

    let h_zm := zero_mul y
    let h_za := zero_add y
    let h_rhs_cong_imp := PeanoEquality.cong_add (0 * V y) 0 (V y) (V y)
    let h_rhs_cong := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_rhs_cong_imp h_zm) (EqualityDeduction.refl (V y))
    let h_rhs_trans_imp := EqualityDeduction.trans (0 * V y + V y) (0 + V y) (V y)
    let h_rhs := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_rhs_trans_imp h_rhs_cong) h_za
    let h_rhs_symm := MinimalFOLDeduction.mp (EqualityDeduction.symm (0 * V y + V y) (V y)) h_rhs

    let h_total_trans_imp := EqualityDeduction.trans (S' 0 * V y) (V y) (0 * V y + V y)
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_total_trans_imp h_one_mul) h_rhs_symm

  let h_step_imp : ⊢ p ⇒ p⟦x := S' (V x)⟧ := by
    have h_subst : p⟦x := S' (V x)⟧ = (S' (S' (V x)) * V y ≃ ((S' (V x) * V y) + V y)) := by
      unfold p
      simp (config := { decide := true }) only [peanoEq, HMul.hMul, Mul.mul, succ, V, HAdd.hAdd,
        Add.add, substF, List.map, substT, BEq.rfl, ↓reduceIte, h_neq', Bool.false_eq_true]
    rw [h_subst]
    apply MinimalFOLDeduction.deduction
    intro h_ih

    let q : Formula PeanoSignature α := (S'(S'(V x)) * V y) ≃ ((S'(V x) * V y) + V y)

    let q_base : ⊢ q⟦y := 0⟧ := by
      unfold q substF
      simp (config := { decide := true }) only [peanoEq, HMul.hMul, Mul.mul, succ, V, HAdd.hAdd,
        Add.add, List.map, OfNat.ofNat, substT, BEq.comm, h_neq', Bool.false_eq_true, ↓reduceIte,
        BEq.rfl]
      let r1 := PeanoDeduction.mul_zero (S'(S'(V x)))
      let r2 := PeanoDeduction.mul_zero (S'(V x))
      let r3 := PeanoDeduction.add_zero (S'(V x) * 0)

      -- Chain: S'S'x * 0 ≃ 0 ≃ S'x * 0 ≃ (S'x * 0) + 0
      let r_mid_imp := EqualityDeduction.trans (S'(S'(V x)) * 0) 0 (S'(V x) * 0 + 0)
      let r_mid2_imp := EqualityDeduction.trans 0 (S'(V x) * 0) (S'(V x) * 0 + 0)
      let r_mid2 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp r_mid2_imp (MinimalFOLDeduction.mp (EqualityDeduction.symm (S'(V x) * 0) 0) r2)) (MinimalFOLDeduction.mp (EqualityDeduction.symm (S'(V x) * 0 + 0) (S'(V x) * 0)) r3)
      exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp r_mid_imp r1) r_mid2

    have q_step_imp : ⊢ q ⇒ q⟦y := S' (V y)⟧ := by
      have h_sub : q⟦y := S' (V y)⟧ = (S' (S' (V x)) * S' (V y) ≃ (S' (V x) * S' (V y)) + S' (V y)) := by
        unfold q substF peanoEq V
        simp (config := { decide := true }) only [List.map_cons, substT_mul, substT_succ, substT,
          h_neq, Bool.false_eq_true, ↓reduceIte, BEq.rfl, substT_add, List.map_nil]
      rw [h_sub]

      apply MinimalFOLDeduction.deduction
      intro ih_q

      let x'' := S' (S' (V x))
      let x' := S' (V x)

      let h1 := PeanoDeduction.mul_succ x'' (V y)
      let h2_ax := PeanoEquality.cong_add (S' (S' (V x)) * V y) (S' (V x) * V y + V y) (S' (S' (V x))) (S' (S' (V x)))
      let h2 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h2_ax ih_q) (EqualityDeduction.refl _)

      let h_lhs := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) h1) h2
      let h3 := PeanoDeduction.add_succ (S' (V x) * V y + V y) (S' (V x))

      let h_lifted := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) h_lhs) h3
      -- 1. Correct the definitions (No double-wrapping)
      let T_base := S' (V x) * V y

      -- 2. Associativity: (T + y) + S'x ≃ T + (y + S'x)
      -- We use the indices x_idx and y_idx for the freshness proof
      let b1 := add_assoc_terms T_base (V y) (S' (V x)) (by
        apply contains_append_false
        exact VariableSupply.fresh_is_fresh (freeVarsTerm T_base ++ freeVarsTerm (V y)))

      -- 3. The Swap Sandwich: y + S'x ≃ S'x + y
      -- a. y + S'x ≃ S' (y + x)
      let s1 := PeanoDeduction.add_succ (V y) (V x)

      -- b. y + x ≃ x + y (Variable level)
      -- Use indices x and y directly to match 'BEq α'
      let h_neq_xy : (x == y) = false := by rw [BEq.comm]; exact h_neq
      let s2_inner := add_comm y x h_neq_xy
      let s2 := MinimalFOLDeduction.mp (PeanoEquality.cong_succ _ _) s2_inner

      -- c. S' (x + y) ≃ S'x + y (Using your clean succ_add_terms)
      let s3_symm := succ_add_terms (V x) (V y) (by
        exact VariableSupply.fresh_is_fresh (freeVarsTerm (V x)))
      let s3 := MinimalFOLDeduction.mp (EqualityDeduction.symm _ _) s3_symm

      -- Combine Sandwich: y + S'x ≃ S'x + y
      let swap_val := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) s1) (MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) s2) s3)

      let b2 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_add T_base T_base _ _) (EqualityDeduction.refl T_base)) swap_val

      -- 2. Shift parentheses back left: T + (S'x + y) ≃ (T + S'x) + y
      let b3_symm := add_assoc_terms T_base (S' (V x)) (V y) (by
        apply contains_append_false
        exact VariableSupply.fresh_is_fresh (freeVarsTerm T_base ++ freeVarsTerm (S' (V x))))
      let b3 := MinimalFOLDeduction.mp (EqualityDeduction.symm _ _) b3_symm

      -- 3. Combine the bridge steps and lift to the successor level
      let bridge_inner := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) b1) (MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) b2) b3)
      let bridge := MinimalFOLDeduction.mp (PeanoEquality.cong_succ _ _) bridge_inner

      -- 4. Connect to our main proof line
      -- Current result: S'S'x * S'y ≃ S' ((T_base + S'x) + y)
      let h_bridged := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) h_lifted) bridge

      -- 5. Successor Sinking: S' ( (T_base + S'x) + y ) ≃ (T_base + S'x) + S'y
      let h_sink_ax := PeanoDeduction.add_succ (T_base + S' (V x)) (V y)
      let h_sink := MinimalFOLDeduction.mp (EqualityDeduction.symm _ _) h_sink_ax

      -- Now the relay works: [LHS ≃ S'(...)] + [S'(...) ≃ Target]
      let c1 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) h_bridged) h_sink

      -- 6. Match Multiplication Definition: (T_base + S'x) + S'y ≃ (S'x * S'y) + S'y
      -- We need to flip the mul_succ axiom here too!
      let def_mul_ax := PeanoDeduction.mul_succ (S' (V x)) (V y)
      let def_mul_symm := MinimalFOLDeduction.mp (EqualityDeduction.symm _ _) def_mul_ax

      let h_final_match_ax := PeanoEquality.cong_add (T_base + S' (V x)) (S' (V x) * S' (V y)) (S' (V y)) (S' (V y))
      let h_final_match := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_final_match_ax def_mul_symm) (EqualityDeduction.refl (S' (V y)))

      -- 7. Final Transitivity to Close the Goal
      exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) c1) h_final_match

    let h_q := forall_elim_simple y (MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoDeduction.induction q y) q_base) (rule_gen_simple y q_step_imp))
    exact h_q

  let h_step : ⊢ ∀' x, p ⇒ p⟦x := S' (V x)⟧ := rule_gen_simple x h_step_imp
  let h_ind_schema := PeanoDeduction.induction p x
  let h_all := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_ind_schema h_base) h_step
  exact forall_elim_simple x h_all

theorem add_mul (x y z : α) (h_xy : (x == y) = false) (h_yz : (y == z) = false) (h_zx : (z == x) = false) [PeanoEquality α] :
  ⊢ ((V x + V y) * V z) ≃ ((V x * V z) + (V y * V z)) := by
  let p : Formula PeanoSignature α := ((V x + V y) * V z) ≃ ((V x * V z) + (V y * V z))

  have h_base : ⊢ p⟦z := 0⟧ := by
    have h_sub : p⟦z := 0⟧ = ((V x + V y) * 0 ≃ V x * 0 + V y * 0) := by
      unfold p substF peanoEq V
      have h_zy : (z == y) = false := by rw [BEq.comm]; exact h_yz
      simp (config := { decide := true }) only [List.map_cons, substT_mul, substT_add, substT, h_zx, h_zy,
        Bool.false_eq_true, ↓reduceIte, BEq.rfl, List.map_nil]
    rw [h_sub]
    let lhs_to_zero := PeanoDeduction.mul_zero (V x + V y)

    let rx_to_zero := PeanoDeduction.mul_zero (V x)
    let ry_to_zero := PeanoDeduction.mul_zero (V y)
    let rhs_cong := MinimalFOLDeduction.mp
      (MinimalFOLDeduction.mp (PeanoEquality.cong_add _ _ _ _) rx_to_zero)
      ry_to_zero

    let zero_add_zero := PeanoDeduction.add_zero (0 : Term PeanoSignature α)
    let rhs_to_zero := MinimalFOLDeduction.mp
      (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) rhs_cong)
      zero_add_zero

    let zero_to_rhs := MinimalFOLDeduction.mp (EqualityDeduction.symm _ _) rhs_to_zero

    exact MinimalFOLDeduction.mp
      (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) lhs_to_zero)
      zero_to_rhs

  have h_step_imp : ⊢ p ⇒ p⟦z := S' (V z)⟧ := by
    have h_sub : p⟦z := S' (V z)⟧ = ((V x + V y) * S' (V z) ≃ (V x * S' (V z)) + (V y * S' (V z))) := by
      unfold p substF peanoEq V
      have h_zy : (z == y) = false := by rw [BEq.comm]; exact h_yz
      have h_yx : (y == x) = false := by rw [BEq.comm]; exact h_xy
      simp (config := { decide := true }) only [List.map_cons, substT_mul, substT_add, substT, h_zy, h_zx,
        Bool.false_eq_true, ↓reduceIte, BEq.rfl, List.map_nil]
    rw[h_sub]
    apply MinimalFOLDeduction.deduction
    intro h_ih
    -- 1. Setup shorthand for the four terms
    let A := V x * V z
    let B := V y * V z
    let C := V x
    let D := V y

    -- 2. LHS Expansion (Targeting (A + B) + (C + D))
    let h_lhs_exp := PeanoDeduction.mul_succ (V x + V y) (V z)
    let h_ih_cong := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_add _ _ _ _) h_ih) (EqualityDeduction.refl (V x + V y))
    let h_lhs_total := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) h_lhs_exp) h_ih_cong

    -- 3. The Shuffle: (A + B) + (C + D) ≃ (A + C) + (B + D)
    -- Step A: (A + B) + (C + D) ≃ ((A + B) + C) + D
    let s1 := MinimalFOLDeduction.mp (EqualityDeduction.symm _ _) (add_assoc_terms (A + B) C D (by
      apply contains_append_false
      exact VariableSupply.fresh_is_fresh (freeVarsTerm (A + B) ++ freeVarsTerm C)))

    -- Step B: ((A + B) + C) + D ≃ (A + (B + C)) + D
    let s2_inner := add_assoc_terms A B C (by
      apply contains_append_false
      exact VariableSupply.fresh_is_fresh (freeVarsTerm A ++ freeVarsTerm B))
    let s2 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_add _ _ D D) s2_inner) (EqualityDeduction.refl D)

    -- Step C: (A + (B + C)) + D ≃ (A + (C + B)) + D (Using your sorried add_comm_terms)
    let s3_swap := add_comm_terms B C (by exact VariableSupply.fresh_is_fresh (freeVarsTerm B))
    let s3_inner := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_add A A _ _) (EqualityDeduction.refl A)) s3_swap
    let s3 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_add _ _ D D) s3_inner) (EqualityDeduction.refl D)

    -- Step D: (A + (C + B)) + D ≃ ((A + C) + B) + D
    let s4_inner_symm := add_assoc_terms A C B (by
      apply contains_append_false
      exact VariableSupply.fresh_is_fresh (freeVarsTerm A ++ freeVarsTerm C))
    let s4_inner := MinimalFOLDeduction.mp (EqualityDeduction.symm _ _) s4_inner_symm
    let s4 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_add _ _ D D) s4_inner) (EqualityDeduction.refl D)

    -- Step E: ((A + C) + B) + D ≃ (A + C) + (B + D)
    let s5 := add_assoc_terms (A + C) B D (by
      apply contains_append_false
      exact VariableSupply.fresh_is_fresh (freeVarsTerm (A + C) ++ freeVarsTerm B))

    -- 4. Combine Shuffle: (A + B) + (C + D) ≃ (A + C) + (B + D)
    let h_shuff_1 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) s1) s2
    let h_shuff_2 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) h_shuff_1) s3
    let h_shuff_3 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) h_shuff_2) s4
    let h_bridge := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) h_shuff_3) s5

    -- 5. RHS Expansion (A + C) + (B + D) ≃ (x * S'z) + (y * S'z)
    let h_rhs_x := MinimalFOLDeduction.mp (EqualityDeduction.symm _ _) (PeanoDeduction.mul_succ (V x) (V z))
    let h_rhs_y := MinimalFOLDeduction.mp (EqualityDeduction.symm _ _) (PeanoDeduction.mul_succ (V y) (V z))
    let h_rhs_total := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_add _ _ _ _) h_rhs_x) h_rhs_y

    -- 6. Final Chain
    let c1 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) h_lhs_total) h_bridge
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) c1) h_rhs_total

  let h_step : ⊢ ∀' z, p ⇒ p⟦z := S' (V z)⟧ := rule_gen_simple z h_step_imp
  let h_ind_schema := PeanoDeduction.induction p z
  let h_all := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_ind_schema h_base) h_step
  exact forall_elim_simple z h_all

theorem mul_add (x y z : α) (h_xy : (x == y) = false) (h_yz : (y == z) = false) (h_zx : (z == x) = false) [PeanoEquality α] :
  ⊢ (V x * (V y + V z)) ≃ ((V x * V y) + (V x * V z)) := by
  sorry

theorem mul_assoc (x y z : α) (h_xy : (x == y) = false) (h_yz : (y == z) = false) (h_zx : (z == x) = false) [PeanoEquality α] :
  ⊢ ((V x * V y) * V z) ≃ (V x * (V y * V z)) := by
  sorry

theorem mul_comm (x y : α) (h_xy : (x == y) = false) [PeanoEquality α] :
  ⊢ (V x * V y) ≃ (V y * V x) := by
  sorry

end Peano
