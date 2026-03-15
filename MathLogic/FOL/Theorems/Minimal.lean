import MathLogic.FOL.Deduction.Minimal

variable {S : Signature} {α : Type} [BEq α] [MinimalFOLDeduction S α]

-- ==========================================
-- VACUOUS QUANTIFICATION
-- ==========================================

theorem all_vacuous {p : Formula S α} (x : α) : isFreeIn x p = false → ⊢ (∀' x, p) ⇔ p := by
  intro hfree
  have hfwd : ⊢ (∀' x, p) ⇒ p := by
    apply MinimalFOLDeduction.deduction
    exact forall_elim_simple x
  have hbwd : ⊢ p ⇒ (∀' x, p) := by
    let s_ax := MinimalFOLDeduction.dist_imp p (p ⇒ p) p
    let k_ax1 := MinimalFOLDeduction.aff_cons p (p ⇒ p)
    let k_ax2 := MinimalFOLDeduction.aff_cons p p
    let p_imp_p := MinimalFOLDeduction.mp (MinimalFOLDeduction.mp s_ax k_ax1) k_ax2
    exact MinimalFOLDeduction.all_intro x hfree p_imp_p
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro (∀' x, p) p ) hfwd) hbwd

theorem ex_vacuous {p : Formula S α} (x : α) : isFreeIn x p = false → ⊢ (∃' x, p) ⇔ p := by
  intro hfree
  have hfwd : ⊢ (∃' x, p) ⇒ p := by
    apply MinimalFOLDeduction.ex_elim
    exact hfree
    apply MinimalFOLDeduction.deduction
    intro hp
    exact hp
  have hbwd : ⊢ p ⇒ (∃' x, p) := by
    apply MinimalFOLDeduction.deduction
    exact exists_intro_simple x
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro (∃' x, p) p ) hfwd) hbwd

-- ==========================================
-- DISTRIBUTION OVER CONJUNCTION
-- ==========================================

theorem all_conj_dist {p q : Formula S α} (x : α) : ⊢ (∀' x, (p ∧ q)) ⇔ (∀' x, p) ∧ (∀' x, q) := by
  have hfwd : ⊢ (∀' x, (p ∧ q)) ⇒ ((∀' x, p) ∧ (∀' x, q)) := by
    apply MinimalFOLDeduction.deduction
    intro h
    sorry
  have hbwd : ⊢ ((∀' x, p) ∧ (∀' x, q)) ⇒ (∀' x, (p ∧ q)) := by

    sorry
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro (∀' x, (p ∧ q)) ((∀' x, p) ∧ (∀' x, q))) hfwd) hbwd

theorem ex_conj_dist_left {p q : Formula S α} (x : α) : isFreeIn x q = false → ⊢ (∃' x, (p ∧ q)) ⇔ (∃' x, p) ∧ q := by
  intro hfree
  have hfwd : ⊢ (∃' x, (p ∧ q)) ⇒ ((∃' x, p) ∧ q) := by sorry
  have hbwd : ⊢ ((∃' x, p) ∧ q) ⇒ (∃' x, (p ∧ q)) := by sorry
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro (∃' x, (p ∧ q)) ((∃' x, p) ∧ q)) hfwd) hbwd

-- ==========================================
-- DISTRIBUTION OVER DISJUNCTION
-- ==========================================

theorem all_disj_dist_left {p q : Formula S α} (x : α) : isFreeIn x q = false → ⊢ (∀' x, (p ∨ q)) ⇔ (∀' x, p) ∨ q := by
  intro hfree
  have hfwd : ⊢ (∀' x, (p ∨ q)) ⇒ ((∀' x, p) ∨ q) := by sorry
  have hbwd : ⊢ ((∀' x, p) ∨ q) ⇒ (∀' x, (p ∨ q)) := by sorry
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro (∀' x, (p ∨ q)) ((∀' x, p) ∨ q)) hfwd) hbwd

theorem ex_disj_dist {p q : Formula S α} (x : α) : ⊢ (∃' x, (p ∨ q)) ⇔ (∃' x, p) ∨ (∃' x, q) := by
  have hfwd : ⊢ (∃' x, (p ∨ q)) ⇒ ((∃' x, p) ∨ (∃' x, q)) := by sorry
  have hbwd : ⊢ ((∃' x, p) ∨ (∃' x, q)) ⇒ (∃' x, (p ∨ q)) := by sorry
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro (∃' x, (p ∨ q)) ((∃' x, p) ∨ (∃' x, q)) ) hfwd) hbwd

-- ==========================================
-- DISTRIBUTION OVER IMPLICATION
-- ==========================================

theorem all_imp_dist_left {p q : Formula S α} (x : α) : isFreeIn x p = false → ⊢ (∀' x, (p ⇒ q)) ⇔ p ⇒ ∀' x, q := by
  intro hfree
  have hfwd : ⊢ (∀' x, (p ⇒ q)) ⇒ (p ⇒ ∀' x, q) := by sorry
  have hbwd : ⊢ (p ⇒ ∀' x, q) ⇒ (∀' x, (p ⇒ q)) := by sorry
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro (∀' x, (p ⇒ q)) (p ⇒ ∀' x, q) ) hfwd) hbwd

theorem ex_imp_dist_left {p q : Formula S α} (x : α) : isFreeIn x p = false → ⊢ (∃' x, (p ⇒ q)) ⇔ p ⇒ ∃' x, q := by
  intro hfree
  have hfwd : ⊢ (∃' x, (p ⇒ q)) ⇒ (p ⇒ ∃' x, q) := by sorry
  have hbwd : ⊢ (p ⇒ ∃' x, q) ⇒ (∃' x, (p ⇒ q)) := by sorry
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro (∃' x, (p ⇒ q)) (p ⇒ ∃' x, q) ) hfwd) hbwd

theorem all_imp_dist_right {p q : Formula S α} (x : α) : isFreeIn x q = false → ⊢ (∀' x, (p ⇒ q)) ⇔ (∃' x, p) ⇒ q := by
  intro hfree
  have hfwd : ⊢ (∀' x, (p ⇒ q)) ⇒ ((∃' x, p) ⇒ q) := by sorry
  have hbwd : ⊢ ((∃' x, p) ⇒ q) ⇒ (∀' x, (p ⇒ q)) := by sorry
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro (∀' x, (p ⇒ q)) ((∃' x, p) ⇒ q) ) hfwd) hbwd

theorem ex_imp_dist_right {p q : Formula S α} (x : α) : isFreeIn x q = false → ⊢ (∃' x, (p ⇒ q)) ⇔ (∀' x, p) ⇒ q := by
  intro hfree
  have hfwd : ⊢ (∃' x, (p ⇒ q)) ⇒ ((∀' x, p) ⇒ q) := by sorry
  have hbwd : ⊢ ((∀' x, p) ⇒ q) ⇒ (∃' x, (p ⇒ q)) := by sorry
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro (∃' x, (p ⇒ q)) ((∀' x, p) ⇒ q) ) hfwd) hbwd

-- ==========================================
-- NEGATION & DE MORGAN FOR QUANTIFIERS
-- ==========================================

theorem neg_ex_iff_all_neg {p : Formula S α} (x : α) : ⊢ (¬∃' x, p) ⇔ (∀' x, ¬p) := by
  have hfwd : ⊢ (¬∃' x, p) ⇒ (∀' x, ¬p) := by sorry
  have hbwd : ⊢ (∀' x, ¬p) ⇒ (¬∃' x, p) := by sorry
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp (MinimalFOLDeduction.iff_intro (¬∃' x, p) (∀' x, ¬p) ) hfwd) hbwd

theorem neg_all_from_ex_neg {p : Formula S α} (x : α) : ⊢ (∃' x, ¬p) ⇒ ¬∀' x, p := by
  sorry
