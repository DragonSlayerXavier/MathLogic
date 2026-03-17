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

theorem imp_trans {p q r : Formula S α} : (⊢ p ⇒ q) → (⊢ q ⇒ r) → (⊢ p ⇒ r) := by
  intro h1 h2
  let h3 := MinimalFOLDeduction.dist_imp p q r
  let h4 := MinimalFOLDeduction.mp (MinimalFOLDeduction.aff_cons (q ⇒ r) p) h2
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h3 h4) h1

theorem self_imp {p : Formula S α} : ⊢ p ⇒ p := by
  let h1 := MinimalFOLDeduction.dist_imp p (p ⇒ p) p
  let h2 := MinimalFOLDeduction.aff_cons p (p ⇒ p)
  let h3 := MinimalFOLDeduction.aff_cons p p
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h1 h2) h3

theorem conj_intro_imp {p q r : Formula S α} : (⊢ p ⇒ q) → (⊢ p ⇒ r) → (⊢ p ⇒ (q ∧ r)) := by
  intro h1 h2
  let h_ax := MinimalFOLDeduction.conj_intro q r
  let h_p_ax := MinimalFOLDeduction.mp (MinimalFOLDeduction.aff_cons (q ⇒ (r ⇒ (q ∧ r))) p) h_ax
  let h_dist1 := MinimalFOLDeduction.dist_imp p q (r ⇒ (q ∧ r))
  let h_step1 := MinimalFOLDeduction.mp h_dist1 h_p_ax
  let h_step2 := MinimalFOLDeduction.mp h_step1 h1
  let h_dist2 := MinimalFOLDeduction.dist_imp p r (q ∧ r)
  let h_step3 := MinimalFOLDeduction.mp h_dist2 h_step2
  exact MinimalFOLDeduction.mp h_step3 h2

theorem disj_cases {p q r : Formula S α} : (⊢ p ⇒ r) → (⊢ q ⇒ r) → (⊢ (p ∨ q) ⇒ r) := by
  intro hp hq
  let h1 := MinimalFOLDeduction.disj_elim p q r
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h1 hp) hq

theorem modus_tollens {p q : Formula S α} : (⊢ p ⇒ q) → (⊢ ¬q ⇒ ¬p) := by
  intro h
  apply MinimalFOLDeduction.deduction
  intro hnq
  apply MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_intro p)
  apply MinimalFOLDeduction.deduction
  intro hp
  let hq := MinimalFOLDeduction.mp h hp
  let h_elim := MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_elim q) hnq
  exact MinimalFOLDeduction.mp h_elim hq

theorem all_imp_dist {p q : Formula S α} (x : α) : ⊢ (∀' x, p ⇒ q) ⇒ (∀' x, p) ⇒ (∀' x, q) := by
  apply MinimalFOLDeduction.deduction
  intro h_all_pq
  apply MinimalFOLDeduction.deduction
  intro h_all_p
  let h_pq_elim := MinimalFOLDeduction.all_elim x (!x) (MinimalFOLDeduction.free_for_self (p ⇒ q) x)
  let h_p_elim := MinimalFOLDeduction.all_elim x (!x) (MinimalFOLDeduction.free_for_self p x)
  rw [MinimalFOLDeduction.subst_self] at h_pq_elim
  rw [MinimalFOLDeduction.subst_self] at h_p_elim
  let h_pq := MinimalFOLDeduction.mp h_pq_elim h_all_pq
  let h_p := MinimalFOLDeduction.mp h_p_elim h_all_p
  let h_q := MinimalFOLDeduction.mp h_pq h_p
  let h_target : ⊢ ⊤ ⇒ q := MinimalFOLDeduction.deduction (λ _ => h_q)
  let h_all_q := MinimalFOLDeduction.all_intro x (by simp [isFreeIn]) h_target
  exact MinimalFOLDeduction.mp h_all_q MinimalFOLDeduction.trivial

theorem all_swap {p : Formula S α} (x y : α) [LawfulBEq α] : ⊢ (∀' x, ∀' y, p) ⇒ (∀' y, ∀' x, p) := by
  apply MinimalFOLDeduction.deduction
  intro h
  let h_elim_x := MinimalFOLDeduction.all_elim x (!x) (MinimalFOLDeduction.free_for_self (∀' y, p) x)
  let h_elim_y := MinimalFOLDeduction.all_elim y (!y) (MinimalFOLDeduction.free_for_self p y)
  rw [MinimalFOLDeduction.subst_self] at h_elim_x
  rw [MinimalFOLDeduction.subst_self] at h_elim_y
  let h_p := MinimalFOLDeduction.mp h_elim_y (MinimalFOLDeduction.mp h_elim_x h)
  let h_inner_imp : ⊢ ⊤ ⇒ p := MinimalFOLDeduction.deduction (λ _ => h_p)
  let h_all_x := MinimalFOLDeduction.all_intro x (by simp [isFreeIn]) h_inner_imp
  let h_val_x := MinimalFOLDeduction.mp h_all_x MinimalFOLDeduction.trivial
  let h_outer_imp : ⊢ ⊤ ⇒ (∀' x, p) := MinimalFOLDeduction.deduction (λ _ => h_val_x)
  let h_all_y := MinimalFOLDeduction.all_intro y (by simp [isFreeIn]) h_outer_imp
  exact MinimalFOLDeduction.mp h_all_y MinimalFOLDeduction.trivial

theorem disj_mono {p q r s : Formula S α} : (⊢ p ⇒ r) → (⊢ q ⇒ s) → (⊢ (p ∨ q) ⇒ (r ∨ s)) := by
  intro hp hq
  -- We need to prove p ⇒ (r ∨ s) and q ⇒ (r ∨ s)
  let h_p_rs := imp_trans hp (MinimalFOLDeduction.disj_intro_left r s)
  let h_q_rs := imp_trans hq (MinimalFOLDeduction.disj_intro_right r s)
  exact disj_cases h_p_rs h_q_rs

theorem all_imp_dist_rule {p q : Formula S α} (x : α) : (⊢ p ⇒ q) → (⊢ (∀' x, p) ⇒ (∀' x, q)) := by
  intro h
  let h_k := @all_imp_dist S α _ _ p q x
  let h_gen_imp : ⊢ ⊤ ⇒ (p ⇒ q) := MinimalFOLDeduction.deduction (λ _ => h)
  let h_all_pq_imp := MinimalFOLDeduction.all_intro x (by simp [isFreeIn]) h_gen_imp
  let h_all_pq := MinimalFOLDeduction.mp h_all_pq_imp MinimalFOLDeduction.trivial
  exact MinimalFOLDeduction.mp h_k h_all_pq

theorem ex_imp_dist_rule {p q : Formula S α} (x : α) [LawfulBEq α] : (⊢ p ⇒ q) → (⊢ (∃' x, p) ⇒ (∃' x, q)) := by
  intro h
  let h_ex_intro := MinimalFOLDeduction.ex_intro x (!x) (MinimalFOLDeduction.free_for_self q x)
  rw [MinimalFOLDeduction.subst_self] at h_ex_intro
  let h_p_ex_q := imp_trans h h_ex_intro
  exact MinimalFOLDeduction.ex_elim x (by simp [isFreeIn]) h_p_ex_q

theorem imp_uncurry {p q r : Formula S α} : ⊢ (p ⇒ (q ⇒ r)) ⇒ ((p ∧ q) ⇒ r) := by
  apply MinimalFOLDeduction.deduction
  intro h_p_q_r
  apply MinimalFOLDeduction.deduction
  intro h_pq
  let hp := MinimalFOLDeduction.mp (MinimalFOLDeduction.conj_elim_left p q) h_pq
  let hq := MinimalFOLDeduction.mp (MinimalFOLDeduction.conj_elim_right p q) h_pq
  exact MinimalFOLDeduction.mp (MinimalFOLDeduction.mp h_p_q_r hp) hq
