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

theorem zero_mul_terms (t : Term PeanoSignature α) [PeanoEquality α] [VariableSupply α] :
  ⊢ 0 * t ≃ 0 := by
  let z := VariableSupply.fresh (freeVarsTerm t)
  let p : Formula PeanoSignature α := 0 * V z ≃ 0

  -- Use 'have' with 'rfl' to prove that the substitution is definitionally what we want
  have h_sub_base : p⟦z := 0⟧ = (0 * 0 ≃ 0) := by
    unfold p substF peanoEq
    -- 1. Use 'congr' to move past the Formula/List wrapper
    congr
    -- 2. Expose the list elements
    simp only [List.map_cons, List.map_nil]
    -- 3. Resolve substitution patterns
    rw [substT_mul, substT_var_same]
    -- 4. Bridge the gap between 'Term.func ... []' and '0'
    -- You may need to add your specific notation names here (e.g., OfNat.ofNat, Zero.zero)
    unfold substT
    simp only [OfNat.ofNat, List.map_nil]

  have h_sub_step : p⟦z := S' (V z)⟧ = (0 * S' (V z) ≃ 0) := by
    unfold p substF peanoEq
    congr
    simp only [List.map_cons, List.map_nil]
    rw [substT_mul, substT_var_same]
    unfold substT
    simp only [OfNat.ofNat, List.map_nil, succ]

  have h_sub_final : p⟦z := t⟧ = (0 * t ≃ 0) := by
    unfold p substF peanoEq
    congr
    simp only [List.map_cons, List.map_nil]
    rw [substT_mul, substT_var_same]
    unfold substT
    simp only [OfNat.ofNat, List.map_nil]


  have h_base : ⊢ p⟦z := 0⟧ := by
    rw [h_sub_base]
    exact PeanoDeduction.mul_zero 0

  have h_step_imp : ⊢ p ⇒ p⟦z := S' (V z)⟧ := by
    rw [h_sub_step]
    apply MinimalFOLDeduction.deduction
    intro ih
    -- FIX: cong_add needs the terms it is relating.
    -- ih has type ⊢ 0 * V z ≃ 0, so we use those terms.
    let l1 := PeanoDeduction.mul_succ 0 (V z)

    -- cong_add expects: (LHS_of_ih) (RHS_of_ih) (Term_to_add_LHS) (Term_to_add_RHS)
    -- Your ih relates (0 * V z) to 0. You want to add 0 to both sides.
    let l2_ax := PeanoEquality.cong_add (0 * V z) 0 0 0

    -- Now mp will work because the first argument matches ih's type
    let l2 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp l2_ax ih) (EqualityDeduction.refl 0)

    let l3 := PeanoDeduction.add_zero (0: Term PeanoSignature α)

    let c1 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) l1) l2
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) c1) l3

  let h_step := rule_gen_simple z h_step_imp
  let h_all := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoDeduction.induction p z) h_base) h_step

  -- Use the 4-argument elimination. Ensure t is free for z.
  let inst := forall_elim z t (by unfold p isFreeFor; rfl) h_all
  rw [h_sub_final] at inst
  exact inst

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

theorem succ_mul_terms (t1 t2 : Term PeanoSignature α) [PeanoEquality α] [VariableSupply α]
  {z : α} (h_z : (freeVarsTerm t1).contains z = false := by
    simp [VariableSupply.fresh_is_fresh, List.contains_append, h_z]
    try exact (VariableSupply.fresh_is_fresh _).1) :
  ⊢ S' t1 * t2 ≃ (t1 * t2) + t2 := by
  let p : Formula PeanoSignature α := S' t1 * V z ≃ (t1 * V z) + V z

  have h_sub_base : p⟦z := 0⟧ = (S' t1 * 0 ≃ (t1 * 0) + 0) := by
    unfold p substF peanoEq
    congr
    simp only [List.map_cons, List.map_nil]
    rw [substT_mul, substT_add, substT_succ, substT_mul, substT_var_same]
    rw [substT_id t1 z 0 h_z]

  have h_sub_step : p⟦z := S' (V z)⟧ = (S' t1 * S' (V z) ≃ (t1 * S' (V z)) + S' (V z)) := by
    unfold p substF peanoEq
    congr
    simp only [List.map_cons, List.map_nil]
    rw [substT_mul, substT_add, substT_succ, substT_mul, substT_var_same]
    rw [substT_id t1 z (S' (V z)) h_z]

  have h_base : ⊢ p⟦z := 0⟧ := by
    rw [h_sub_base]
    let l1 := PeanoDeduction.mul_zero (S' t1)
    let r1 := PeanoDeduction.mul_zero t1
    let r2_ax := PeanoEquality.cong_add (t1 * 0) 0 0 0
    let r2 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp r2_ax r1) (EqualityDeduction.refl 0)
    let r3 := PeanoDeduction.add_zero (0: Term PeanoSignature α)
    let r_total := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) r2) r3
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) l1)
            (MinimalFOLDeduction.mp (EqualityDeduction.symm _ _) r_total)

  have h_step_imp : ⊢ p ⇒ p⟦z := S' (V z)⟧ := by
    rw [h_sub_step]
    apply MinimalFOLDeduction.deduction
    intro ih
    let A := t1 * V z
    let B := V z
    let C := t1
    let l1 := PeanoDeduction.mul_succ (S' t1) (V z)
    let l2_ax := PeanoEquality.cong_add (S' t1 * V z) (A + B) (S' C) (S' C)
    let l2 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp l2_ax ih) (EqualityDeduction.refl (S' C))
    let lhs_final := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) l1) l2
    let r1_inner := PeanoDeduction.mul_succ t1 (V z)
    let r1_ax := PeanoEquality.cong_add (t1 * S' (V z)) (A + C) (S' B) (S' B)
    let r1 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp r1_ax r1_inner) (EqualityDeduction.refl (S' B))

    -- The Shuffle Bridge: ((A+B) + S'C) ≃ ((A+C) + S'B)
    let s1 := add_assoc_terms A B (S' C) (by
      apply contains_append_false
      exact VariableSupply.fresh_is_fresh (freeVarsTerm A ++ freeVarsTerm B))

    let s2_comm := add_comm_terms B (S' C) (by
      exact VariableSupply.fresh_is_fresh (freeVarsTerm B))
    let s2 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_add A A _ _)
                (EqualityDeduction.refl A)) s2_comm -- A+(B+S'C) ≃ A+(S'C+B)

    let s3_succ := succ_add_terms C B (by exact VariableSupply.fresh_is_fresh (freeVarsTerm C))
    let s3 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_add A A _ _)
                (EqualityDeduction.refl A)) s3_succ -- A+(S'C+B) ≃ A+S'(C+B)

    -- Successor Commutativity
    let s4_comm := add_comm_terms C B
    let s4 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_add A A _ _)
                (EqualityDeduction.refl A))
                (MinimalFOLDeduction.mp (PeanoEquality.cong_succ _ _) s4_comm) -- A+S'(C+B) ≃ A+S'(B+C)

    -- s5: Using MP for Symmetry
    let s5_symm_ax := EqualityDeduction.symm (S' B + C) (S' (B + C))
    let s5_succ := MinimalFOLDeduction.mp s5_symm_ax (succ_add_terms B C (by exact VariableSupply.fresh_is_fresh (freeVarsTerm B)))
    let s5 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_add A A _ _)
                (EqualityDeduction.refl A)) s5_succ -- A+S'(B+C) ≃ A+(S'B+C)

    let s6_comm := add_comm_terms (S' B) C (by exact VariableSupply.fresh_is_fresh (freeVarsTerm (S' B)))
    let s6 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_add A A _ _)
                (EqualityDeduction.refl A)) s6_comm -- A+(S'B+C) ≃ A+(C+S'B)

    -- s7: Corrected symmetry for associativity
    let s7_symm_ax := EqualityDeduction.symm ((A + C) + S' B) (A + (C + S' B))
    let s7 := MinimalFOLDeduction.mp s7_symm_ax (add_assoc_terms A C (S' B) (by
      apply contains_append_false
      exact VariableSupply.fresh_is_fresh (freeVarsTerm A ++ freeVarsTerm C)))

    -- Transitivity Chain
    let bridge := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _)
                    (MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) s1) s2))
                    (MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) s3)
                    (MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) s4)
                    (MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) s5)
                    (MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) s6) s7))))

    let l1 := PeanoDeduction.mul_succ (S' t1) (V z)

    let l2_cong := PeanoEquality.cong_add (S' t1 * V z) (A + B) (S' C) (S' C)
    let l2 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp l2_cong ih) (EqualityDeduction.refl (S' C))

    let lhs_trans_ax := EqualityDeduction.trans (S' t1 * S' (V z)) ((S' t1 * V z) + S' t1) ((A + B) + S' C)
    let lhs_final := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp lhs_trans_ax l1) l2

    let r1_inner := PeanoDeduction.mul_succ t1 (V z)

    let r1_cong := PeanoEquality.cong_add (t1 * S' (V z)) (A + C) (S' B) (S' B)
    let r1 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp r1_cong r1_inner) (EqualityDeduction.refl (S' B))

    let rhs_final := r1

    let final_trans_ax1 := EqualityDeduction.trans (S' t1 * S' (V z)) ((A + B) + S' C) ((A + C) + S' B)
    let left_to_bridge := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp final_trans_ax1 lhs_final) bridge

    let final_trans_ax2 := EqualityDeduction.trans (S' t1 * S' (V z)) ((A + C) + S' B) ((t1 * S' (V z)) + S' (V z))
    let symm_ax := EqualityDeduction.symm ((t1 * S' (V z)) + S' (V z)) ((A + C) + S' B)
    let rhs_symm := MinimalFOLDeduction.mp symm_ax rhs_final

    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp final_trans_ax2 left_to_bridge) rhs_symm

  let h_step := rule_gen_simple z h_step_imp
  let h_all := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoDeduction.induction p z) h_base) h_step
  let inst := forall_elim z t2 (by unfold p isFreeFor; rfl) h_all
  have h_final : p⟦z := t2⟧ = (S' t1 * t2 ≃ (t1 * t2) + t2) := by
    unfold p substF peanoEq
    congr
    simp only [List.map_cons, List.map_nil]
    rw [substT_mul, substT_add, substT_succ, substT_mul, substT_var_same]
    rw [substT_id t1 z t2 h_z]
  rw [h_final] at inst
  exact inst

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
  let p : Formula PeanoSignature α := (V x * (V y + V z)) ≃ ((V x * V y) + (V x * V z))
  let h_yx : (y == x) = false := by rw [BEq.comm]; exact h_xy
  let h_zy : (z == y) = false := by rw [BEq.comm]; exact h_yz
  let h_xz : (x == z) = false := by rw [BEq.comm]; exact h_zx
  have h_base : ⊢ p⟦y := 0⟧ := by
    have h_sub : p⟦y := 0⟧ = (V x * (0 + V z) ≃ (V x * 0) + (V x * V z)) := by
      unfold p substF peanoEq V
      simp (config := { decide := true }) only [substT_mul, substT_add, substT, h_yx, h_yz,
        Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, BEq.rfl]
    rw [h_sub]
    let h_l1 := zero_add_terms (V z) (z := y)
    let h_lhs := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_mul (V x) (V x) _ _)
                  (EqualityDeduction.refl (V x))) h_l1

    let h_r1 := PeanoDeduction.mul_zero (V x)
    let h_r2 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_add _ _ _ _) h_r1)
                  (EqualityDeduction.refl (V x * V z))

    let h_y_fresh_xz : (freeVarsTerm (V x * V z)).contains y = false := by
      unfold freeVarsTerm V
      simp (config := { decide := true }) only [List.flatMap_cons, freeVarsTerm, List.flatMap_nil,
        List.append_nil, List.cons_append, List.nil_append, List.contains_eq_mem, List.mem_cons,
        List.not_mem_nil, or_false, List.decide_mem_cons, h_yx, h_yz, decide_false, Bool.or_self]

    let h_l1 := zero_add_terms (V z) (z := y)
    let h_lhs := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_mul (V x) (V x) _ _)
                  (EqualityDeduction.refl (V x))) h_l1

    let h_r1 := PeanoDeduction.mul_zero (V x)
    let h_r2 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_add _ _ _ _) h_r1)
                  (EqualityDeduction.refl (V x * V z))

    let h_r3 := zero_add_terms (V x * V z) (z := y)
    let h_rhs_total := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) h_r2) h_r3

    let h_final := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) h_lhs)
                    (MinimalFOLDeduction.mp (EqualityDeduction.symm _ _) h_rhs_total)
    exact h_final
  have h_step_imp : ⊢ p ⇒ p⟦y := S' (V y)⟧ := by
    have h_sub : p⟦y := S' (V y)⟧ = (V x * (S' (V y) + V z) ≃ (V x * S' (V y)) + (V x * V z)) := by
      unfold p substF peanoEq V
      simp (config := { decide := true }) only [substT_mul, substT_add, substT, h_yx, h_yz,
        Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, BEq.rfl]
    rw [h_sub]
    apply MinimalFOLDeduction.deduction
    intro ih

    let h_s_add := succ_add_terms (V y) (V z) (z := z) (h_z := by unfold freeVarsTerm V; simp only [List.contains_eq_mem,
      List.mem_cons, List.not_mem_nil, or_false, List.decide_mem_cons, BEq.comm, h_yz, decide_false,
      Bool.or_self])

    let h_l1 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_mul (V x) (V x) _ _)
                  (EqualityDeduction.refl (V x))) h_s_add

    let h_l2 := PeanoDeduction.mul_succ (V x) (V y + V z)

    let h_ih_ax := PeanoEquality.cong_add (V x * (V y + V z)) (V x * V y + V x * V z) (V x) (V x)
    let h_l3 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_ih_ax ih) (EqualityDeduction.refl (V x))

    let h_lhs_total := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) h_l1)
                        (MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) h_l2) h_l3)

    let h_r1_ax := PeanoDeduction.mul_succ (V x) (V y)
    let h_rhs_total := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_add _ _ _ _) h_r1_ax)
                        (EqualityDeduction.refl (V x * V z))

    let A := V x * V y
    let B := V x * V z
    let C := V x

    let s1 := add_assoc_terms A B C (by
      apply contains_append_false
      exact VariableSupply.fresh_is_fresh (freeVarsTerm A ++ freeVarsTerm B))

    let s2_comm := add_comm_terms B C (by
      exact VariableSupply.fresh_is_fresh (freeVarsTerm B))

    let s2 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_add A A _ _)
                (EqualityDeduction.refl A)) s2_comm

    let s3_symm := add_assoc_terms A C B (by
      apply contains_append_false
      exact VariableSupply.fresh_is_fresh (freeVarsTerm A ++ freeVarsTerm C))
    let s3 := MinimalFOLDeduction.mp (EqualityDeduction.symm _ _) s3_symm

    -- 5. Combine the shuffle chain
    let h_shuffle := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) s1)
                      (MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) s2) s3)

    -- LHS ≃ ((A+B)+C) ≃ ((A+C)+B) ≃ RHS
    let c1 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) h_lhs_total) h_shuffle
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) c1)
            (MinimalFOLDeduction.mp (EqualityDeduction.symm _ _) h_rhs_total)
  let h_step : ⊢ ∀' y, p ⇒ p⟦y := S' (V y)⟧ := rule_gen_simple y h_step_imp
  let h_ind_schema := PeanoDeduction.induction p y
  let h_all := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_ind_schema h_base) h_step
  exact forall_elim_simple y h_all

theorem mul_add_terms (t1 t2 t3 : Term PeanoSignature α) [PeanoEquality α] [VariableSupply α]
  {z : α} (h_z : (freeVarsTerm t1).contains z = false ∧ (freeVarsTerm t2).contains z = false := by
    apply contains_append_false
    exact VariableSupply.fresh_is_fresh _
  ) :
  ⊢ (t1 * (t2 + t3)) ≃ ((t1 * t2) + (t1 * t3)) := by
  let p : Formula PeanoSignature α := (t1 * (t2 + V z)) ≃ ((t1 * t2) + (t1 * V z))

  -- The base case: t1 * (t2 + 0) ≃ (t1 * t2) + (t1 * 0)
  have h_base : ⊢ p⟦z := 0⟧ := by
    have h_sub : p⟦z := 0⟧ = (t1 * (t2 + 0) ≃ (t1 * t2) + (t1 * 0)) := by
      unfold p substF peanoEq V
      simp (config := { decide := true }) only [List.map_cons, substT_mul, substT_add, substT,
        BEq.rfl, ↓reduceIte, List.map_nil, Formula.pred.injEq, List.cons.injEq, and_true, true_and]
      rw [substT_id t1 z 0 h_z.1]
      rw [substT_id t2 z 0 h_z.2]
      simp only [and_self]
    rw [h_sub]
    -- LHS: t1 * (t2 + 0) ≃ t1 * t2
    let l1 := PeanoDeduction.add_zero t2
    let l_total := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_mul t1 t1 _ _)
                    (EqualityDeduction.refl t1)) l1

    -- RHS: (t1 * t2) + (t1 * 0) ≃ (t1 * t2) + 0 ≃ t1 * t2
    let r1 := PeanoDeduction.mul_zero t1
    let r2 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_add _ _ _ _)
                (EqualityDeduction.refl (t1 * t2))) r1
    let r3 := PeanoDeduction.add_zero (t1 * t2)
    let r_total := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) r2) r3

    -- Bridge: LHS ≃ t1*t2 ≃ RHS
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) l_total)
            (MinimalFOLDeduction.mp (EqualityDeduction.symm _ _) r_total)
  have h_step_imp : ⊢ p ⇒ p⟦z := S' (V z)⟧ := by
    have h_sub : p⟦z := S' (V z)⟧ = (t1 * (t2 + S' (V z)) ≃ (t1 * t2) + (t1 * S' (V z))) := by
      unfold p substF peanoEq V
      simp (config := { decide := true }) only [List.map_cons, substT_mul, substT_add, substT,
        BEq.rfl, ↓reduceIte, List.map_nil]
      rw [substT_id t1 z (S' !z) h_z.1]
      rw [substT_id t2 z (S' !z) h_z.2]
    rw[h_sub]
    apply MinimalFOLDeduction.deduction
    intro ih

    let l1 := PeanoDeduction.add_succ t2 (V z)
    let l2 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_mul t1 t1 _ _)
                (EqualityDeduction.refl t1)) l1

    let l3 := PeanoDeduction.mul_succ t1 (t2 + V z)
    let lhs_to_succ := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) l2) l3

    let l4 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_add _ _ t1 t1) ih)
                (EqualityDeduction.refl t1)
    let lhs_final := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) lhs_to_succ) l4

    let r1 := PeanoDeduction.mul_succ t1 (V z)
    let rhs_final := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_add (t1 * t2) (t1 * t2) _ _)
                      (EqualityDeduction.refl (t1 * t2))) r1

    let A := t1 * t2
    let B := t1 * V z
    let C := t1
    let assoc := add_assoc_terms A B C (by
      apply contains_append_false
      exact VariableSupply.fresh_is_fresh (freeVarsTerm A ++ freeVarsTerm B))

    let c1 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) lhs_final) assoc
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) c1)
            (MinimalFOLDeduction.mp (EqualityDeduction.symm _ _) rhs_final)
  let h_step := rule_gen_simple z h_step_imp
  let h_all := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoDeduction.induction p z) h_base) h_step

  -- Use forall_elim to plug in t3 for z
  -- We provide a small proof that t3 is "free for" z (usually handled by rfl if p is simple)
  let inst := forall_elim z t3 (by unfold p peanoEq isFreeFor; rfl) h_all

  -- This step cleans up the substitution so it matches your goal exactly
  have h_final : p⟦z := t3⟧ = (t1 * (t2 + t3) ≃ (t1 * t2) + (t1 * t3)) := by
    unfold p substF peanoEq V
    simp (config := { decide := true }) only [substT_mul, substT_add, substT,
      ↓reduceIte, List.map_cons, List.map_nil, BEq.rfl]
    rw [substT_id t1 z t3 h_z.1, substT_id t2 z t3 h_z.2]

  rw [h_final] at inst
  exact inst

theorem mul_assoc (x y z : α) (h_xy : (x == y) = false) (h_yz : (y == z) = false) (h_zx : (z == x) = false) [PeanoEquality α] :
  ⊢ ((V x * V y) * V z) ≃ (V x * (V y * V z)) := by
  let p : Formula PeanoSignature α := ((V x * V y) * V z) ≃ (V x * (V y * V z))
  let h_yx : (y == x) = false := by rw [BEq.comm]; exact h_xy
  let h_zy : (z == y) = false := by rw [BEq.comm]; exact h_yz
  let h_xz : (x == z) = false := by rw [BEq.comm]; exact h_zx
  have h_base : ⊢ p⟦z := 0⟧ := by
    have h_sub : p⟦z := 0⟧ = ((V x * V y) * 0 ≃ V x * (V y * 0)) := by
      unfold p substF peanoEq V
      simp (config := { decide := true }) only [substT_mul, substT, h_zx, h_zy,
        Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, BEq.rfl]
    rw [h_sub]
    let l := PeanoDeduction.mul_zero (V x * V y)
    let r_inner := PeanoDeduction.mul_zero (V y)
    let r_cong := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_mul (V x) (V x) _ _)
                    (EqualityDeduction.refl (V x))) r_inner
    let r_outer := PeanoDeduction.mul_zero (V x)
    let r_total := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) r_cong) r_outer
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) l)
            (MinimalFOLDeduction.mp (EqualityDeduction.symm _ _) r_total)
  have h_step_imp : ⊢ p ⇒ p⟦z := S' (V z)⟧ := by
    have h_sub : p⟦z := S' (V z)⟧ = ((V x * V y) * S' (V z) ≃ V x * (V y * S' (V z))) := by
      unfold p substF peanoEq V
      simp (config := { decide := true }) only [substT_mul, substT, h_zx, h_zy,
        Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, BEq.rfl]
    rw [h_sub]
    apply MinimalFOLDeduction.deduction
    intro ih

    -- 1. Expand LHS: (x * y) * S'z ≃ ((x * y) * z) + (x * y)
    let l1 := PeanoDeduction.mul_succ (V x * V y) (V z)

    -- 2. Apply IH to LHS: ((x * y) * z) + (x * y) ≃ (V x * (V y * V z)) + (V x * V y)
    let l2_ax := PeanoEquality.cong_add ((V x * V y) * V z) (V x * (V y * V z)) (V x * V y) (V x * V y)
    let l2 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp l2_ax ih) (EqualityDeduction.refl (V x * V y))
    let lhs_final := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) l1) l2

    -- 3. Expand RHS: V x * (V y * S'z) ≃ V x * ((V y * V z) + V y)
    let r1_inner := PeanoDeduction.mul_succ (V y) (V z)
    let r1 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (PeanoEquality.cong_mul (V x) (V x) _ _)
                (EqualityDeduction.refl (V x))) r1_inner

    -- 4. Distribute V x over the inner sum: V x * ((V y * V z) + V y) ≃ (V x * (V y * V z)) + (V x * V y)
    -- We use our new mul_add_terms here!
    let r2 := mul_add_terms (V x) (V y * V z) (V y)
    let rhs_final := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) r1) r2

    -- 5. Final Bridge: LHS ≃ common_term ≃ RHS
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) lhs_final)
            (MinimalFOLDeduction.mp (EqualityDeduction.symm _ _) rhs_final)
  let h_step : ⊢ ∀' z, p ⇒ p⟦z := S' (V z)⟧ := rule_gen_simple z h_step_imp
  let h_ind_schema := PeanoDeduction.induction p z
  let h_all := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_ind_schema h_base) h_step
  exact forall_elim_simple z h_all

theorem mul_comm (x y : α) (h_xy : (x == y) = false) [PeanoEquality α] :
  ⊢ (V x * V y) ≃ (V y * V x) := by
  let p : Formula PeanoSignature α := (V x * V y) ≃ (V y * V x)
  let h_yx : (y == x) = false := by rw [BEq.comm]; exact h_xy
  have h_base : ⊢ p⟦y := 0⟧ := by
    have h_sub : p⟦y := 0⟧ = (V x * 0 ≃ 0 * V x) := by
      unfold p substF peanoEq V
      simp (config := { decide := true }) only [substT_mul, substT, h_yx,
        Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, BEq.rfl]
    rw [h_sub]
    let l := PeanoDeduction.mul_zero (V x)
    let r := zero_mul x
    let symm_ax := EqualityDeduction.symm (0 * V x) 0
    let r_symm := MinimalFOLDeduction.mp symm_ax r
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) l) r_symm
  have h_step_imp : ⊢ p ⇒ p⟦y := S' (V y)⟧ := by
    have h_sub : p⟦y := S' (V y)⟧ = (V x * S' (V y) ≃ S' (V y) * V x) := by
      unfold p substF peanoEq V
      simp (config := { decide := true }) only [substT_mul, substT, h_yx,
        Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, BEq.rfl]
    rw [h_sub]
    apply MinimalFOLDeduction.deduction
    intro ih

    -- 1. Expand LHS: V x * S' (V y) ≃ (V x * V y) + V x
    let l1 := PeanoDeduction.mul_succ (V x) (V y)

    -- 2. Apply IH to LHS: (V x * V y) + V x ≃ (V y * V x) + V x
    let l2_ax := PeanoEquality.cong_add (V x * V y) (V y * V x) (V x) (V x)
    let l2 := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp l2_ax ih) (EqualityDeduction.refl (V x))
    let lhs_final := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) l1) l2

    -- 3. Expand RHS: S' (V y) * V x ≃ (V y * V x) + V x
    -- This is exactly what succ_mul_terms provides
    let rhs_final := succ_mul_terms (V y) (V x) (by exact VariableSupply.fresh_is_fresh (freeVarsTerm (V y)))

    -- 4. Bridge: LHS ≃ middle ≃ RHS
    let symm_ax := EqualityDeduction.symm (S' (V y) * V x) ((V y * V x) + V x)
    let rhs_symm := MinimalFOLDeduction.mp symm_ax rhs_final
    exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (EqualityDeduction.trans _ _ _) lhs_final) rhs_symm
  let h_step : ⊢ ∀' y, p ⇒ p⟦y := S' (V y)⟧ := rule_gen_simple y h_step_imp
  let h_ind_schema := PeanoDeduction.induction p y
  let h_all := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_ind_schema h_base) h_step
  exact forall_elim_simple y h_all

end Peano
