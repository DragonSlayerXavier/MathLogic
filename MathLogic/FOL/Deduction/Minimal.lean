import MathLogic.FOL.Syntax

class MinimalFOLDeduction (S : Signature) (α : Type) [BEq α] where
  Pr : Formula S α → Prop

  -- Rules of Inference
  mp        : ∀ {p q : Formula S α}, Pr (p ⇒ q) → Pr p → Pr q
  deduction : ∀ {p q : Formula S α}, (Pr p → Pr q) → Pr (p ⇒ q)

  -- I. Implication Axioms
  aff_cons : ∀ (p q : Formula S α), Pr (p ⇒ (q ⇒ p))
  dist_imp : ∀ (p q r : Formula S α), Pr ((p ⇒ (q ⇒ r)) ⇒ ((p ⇒ q) ⇒ (p ⇒ r)))

  -- II. Conjunction Axioms
  conj_intro      : ∀ (p q : Formula S α), Pr (p ⇒ (q ⇒ (p ∧ q)))
  conj_elim_left  : ∀ (p q : Formula S α), Pr ((p ∧ q) ⇒ p)
  conj_elim_right : ∀ (p q : Formula S α), Pr ((p ∧ q) ⇒ q)

  -- III. Disjunction Axioms
  disj_intro_left  : ∀ (p q : Formula S α), Pr (p ⇒ (p ∨ q))
  disj_intro_right : ∀ (p q : Formula S α), Pr (q ⇒ (p ∨ q))
  disj_elim        : ∀ (p q r : Formula S α), Pr ((p ⇒ r) ⇒ ((q ⇒ r) ⇒ ((p ∨ q) ⇒ r)))

  -- IV. Negation and Truth Axioms
  trivial   : Pr ⊤
  neg_intro : ∀ (p : Formula S α), Pr ((p ⇒ ⊥) ⇒ ¬p)
  neg_elim  : ∀ (p : Formula S α), Pr (¬p ⇒ (p ⇒ ⊥))

  -- V. IFF Axioms
  iff_intro      : ∀ (p q : Formula S α), Pr ((p ⇒ q) ⇒ ((q ⇒ p) ⇒ (p ⇔ q)))
  iff_elim_left  : ∀ (p q : Formula S α), Pr ((p ⇔ q) ⇒ (p ⇒ q))
  iff_elim_right : ∀ (p q : Formula S α), Pr ((p ⇔ q) ⇒ (q ⇒ p))

  -- VI. Quantifier Axioms
  all_intro : ∀ {p q : Formula S α} (x : α), isFreeIn x p = false → Pr (p ⇒ q) → Pr (p ⇒ (∀' x, q))
  all_elim  : ∀ {p : Formula S α} (x : α) (t : Term S α), isFreeFor t x p = true → Pr ((∀' x, p) ⇒ p⟦x := t⟧)

  ex_intro : ∀ {p : Formula S α} (x : α) (t : Term S α), isFreeFor t x p = true → Pr (p⟦x := t⟧ ⇒ (∃' x, p))
  ex_elim  : ∀ {p q : Formula S α} (x : α), isFreeIn x q = false → Pr (p ⇒ q) → Pr ((∃' x, p) ⇒ q)

  -- VII. Structural Axioms
  subst_self     : ∀ (p : Formula S α) (x : α), p⟦x := !x⟧ = p
  subst_id       : ∀ (p : Formula S α) (x : α) (t : Term S α), isFreeIn x p = false → p⟦x := t⟧ = p
  free_for_self  : ∀ (p : Formula S α) (x : α), isFreeFor (!x) x p = true
  free_for_var   : ∀ (p : Formula S α) (x : α), isFreeIn x p = false → isFreeFor (!x) x p = true

notation:30 "⊢ " p:0 => MinimalFOLDeduction.Pr p

-- ==========================================
-- THEOREMS
-- ==========================================

variable {S : Signature} {α : Type} [BEq α] [MinimalFOLDeduction S α]

theorem rule_gen_simple {p : Formula S α} (x : α) : (⊢ p) → (⊢ ∀' x, p) := by
  intro h
  have h1 : ⊢ ⊤ ⇒ p := MinimalFOLDeduction.deduction (λ _ => h)
  have h2 : ⊢ ⊤ ⇒ ∀' x, p := MinimalFOLDeduction.all_intro x rfl h1
  exact MinimalFOLDeduction.mp h2 MinimalFOLDeduction.trivial

theorem forall_elim_simple {p : Formula S α} (x : α) : (⊢ ∀' x, p) → (⊢ p) := by
  intro h
  let ax := MinimalFOLDeduction.all_elim x (!x) (MinimalFOLDeduction.free_for_self p x)
  let inst := MinimalFOLDeduction.mp ax h
  rw [MinimalFOLDeduction.subst_self] at inst
  exact inst

theorem exists_intro_simple {p : Formula S α} (x : α) : (⊢ p) → (⊢ ∃' x, p) := by
  intro h
  let ax := MinimalFOLDeduction.ex_intro x (!x) (MinimalFOLDeduction.free_for_self p x)
  rw [MinimalFOLDeduction.subst_self] at ax
  exact MinimalFOLDeduction.mp ax h

variable {S : Signature} {α : Type} [BEq α]

-- ==========================================
-- VARIABLE & SUBST DYNAMICS
-- ==========================================

theorem is_free_in_imp (x : α) (p q : Formula S α) :
  isFreeIn x (p ⇒ q) = (isFreeIn x p || isFreeIn x q) := rfl

theorem is_free_in_conj (x : α) (p q : Formula S α) :
  isFreeIn x (p ∧ q) = (isFreeIn x p || isFreeIn x q) := rfl

theorem is_free_in_disj (x : α) (p q : Formula S α) :
  isFreeIn x (p ∨ q) = (isFreeIn x p || isFreeIn x q) := rfl

theorem substF_imp (p q : Formula S α) (x : α) (s : Term S α) :
  (p ⇒ q)⟦x := s⟧ = (p⟦x := s⟧ ⇒ q⟦x := s⟧) := rfl

theorem substF_conj (p q : Formula S α) (x : α) (s : Term S α) :
  (p ∧ q)⟦x := s⟧ = (p⟦x := s⟧ ∧ q⟦x := s⟧) := rfl

theorem substF_disj (p q : Formula S α) (x : α) (s : Term S α) :
  (p ∨ q)⟦x := s⟧ = (p⟦x := s⟧ ∨ q⟦x := s⟧) := rfl

theorem substF_all_same [LawfulBEq α] (p : Formula S α) (x : α) (s : Term S α) :
  (∀' x, p)⟦x := s⟧ = (∀' x, p) := by
  simp [substF]

-- ==========================================
-- QUANTIFIER RULES
-- ==========================================

variable [MinimalFOLDeduction S α]

theorem forall_elim {p : Formula S α} (x : α) (t : Term S α) :
  isFreeFor t x p = true → (⊢ ∀' x, p) → (⊢ p⟦x := t⟧) := by
  intro h_ff h_all
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.all_elim x t h_ff) h_all

theorem exists_intro {p : Formula S α} (x : α) (t : Term S α) :
  isFreeFor t x p = true → (⊢ p⟦x := t⟧) → (⊢ ∃' x, p) := by
  intro h_ff h_inst
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.ex_intro x t h_ff) h_inst

theorem exists_elim {p q : Formula S α} (x : α) :
  (⊢ p ⇒ q) → isFreeIn x q = false → (⊢ (∃' x, p) ⇒ q) := by
  intro h_imp h_nf
  exact MinimalFOLDeduction.ex_elim x h_nf h_imp
