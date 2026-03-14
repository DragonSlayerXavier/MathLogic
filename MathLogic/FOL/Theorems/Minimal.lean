import MathLogic.FOL.Deduction.Minimal

variable {S : Signature} {α : Type} [BEq α] [MinimalFoldeduction S α]

-- ==========================================
-- VACUOUS QUANTIFICATION
-- ==========================================

theorem all_vacuous {p : Formula S α} (x : α) :
  isFreeIn x p = false → ⊢ (∀' x, p) ⇔ p := sorry

theorem ex_vacuous {p : Formula S α} (x : α) :
  isFreeIn x p = false → ⊢ (∃' x, p) ⇔ p := sorry

-- ==========================================
-- DISTRIBUTION OVER CONJUNCTION
-- ==========================================

theorem all_conj_dist {p q : Formula S α} (x : α) :
  ⊢ (∀' x, (p ∧ q)) ⇔ (∀' x, p) ∧ (∀' x, q) := sorry

theorem ex_conj_dist_left {p q : Formula S α} (x : α) :
  isFreeIn x q = false → ⊢ (∃' x, (p ∧ q)) ⇔ (∃' x, p) ∧ q := sorry

-- ==========================================
-- DISTRIBUTION OVER DISJUNCTION
-- ==========================================

theorem all_disj_dist_left {p q : Formula S α} (x : α) :
  isFreeIn x q = false → ⊢ (∀' x, (p ∨ q)) ⇔ (∀' x, p) ∨ q := sorry

theorem ex_disj_dist {p q : Formula S α} (x : α) :
  ⊢ (∃' x, (p ∨ q)) ⇔ (∃' x, p) ∨ (∃' x, q) := sorry

-- ==========================================
-- DISTRIBUTION OVER IMPLICATION
-- ==========================================

theorem all_imp_dist_left {p q : Formula S α} (x : α) :
  isFreeIn x p = false → ⊢ (∀' x, (p ⇒ q)) ⇔ p ⇒ ∀' x, q := sorry

theorem ex_imp_dist_left {p q : Formula S α} (x : α) :
  isFreeIn x p = false → ⊢ (∃' x, (p ⇒ q)) ⇔ p ⇒ ∃' x, q := sorry

theorem all_imp_dist_right {p q : Formula S α} (x : α) :
  isFreeIn x q = false → ⊢ (∀' x, (p ⇒ q)) ⇔ (∃' x, p) ⇒ q := sorry

theorem ex_imp_dist_right {p q : Formula S α} (x : α) :
  isFreeIn x q = false → ⊢ (∃' x, (p ⇒ q)) ⇔ (∀' x, p) ⇒ q := sorry

-- ==========================================
-- NEGATION & DE MORGAN FOR QUANTIFIERS
-- ==========================================

theorem neg_ex_iff_all_neg {p : Formula S α} (x : α) :
  ⊢ ¬∃' x, p ⇔ ∀' x, ¬p := sorry

theorem neg_all_from_ex_neg {p : Formula S α} (x : α) :
  ⊢ (∃' x, ¬p) ⇒ ¬∀' x, p := sorry
