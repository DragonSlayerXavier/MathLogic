import MathLogic.PropLogic.Syntax
import MathLogic.PropLogic.Deduction.Classical
import MathLogic.PropLogic.Theorems.Minimal
import MathLogic.PropLogic.Theorems.Intuitionistic

open Formula
variable {α : Type} [ClassicalDeduction α]

-- I. Fundamental Classical Principles
theorem proof_by_contradiction (A : Formula α) : ⊢ ((¬A ⇒ ⊥) ⇒ A) := by
  apply MinimalDeduction.deduction
  intro h
  have hnna: ⊢ ¬¬A := by
    apply MinimalDeduction.mp (MinimalDeduction.neg_intro (¬A))
    apply MinimalDeduction.deduction
    intro hna
    exact MinimalDeduction.mp h hna
  exact MinimalDeduction.mp (ClassicalDeduction.dne) hnna

theorem ex_falso (A : Formula α) : ⊢ (⊥ ⇒ A) := by
  apply MinimalDeduction.deduction
  intro h
  have hnna: ⊢ ¬¬A := by
    apply MinimalDeduction.mp (MinimalDeduction.neg_intro (¬A))
    apply MinimalDeduction.deduction
    intro hna
    exact h
  exact MinimalDeduction.mp (ClassicalDeduction.dne) hnna

theorem excluded_middle (A : Formula α) : ⊢ (A ∨ ¬A) := by
  apply MinimalDeduction.mp (proof_by_contradiction (A ∨ ¬A))
  apply MinimalDeduction.deduction
  intro h
  have hna: ⊢ ¬A := by
    apply MinimalDeduction.mp (MinimalDeduction.neg_intro A)
    apply MinimalDeduction.deduction
    intro ha
    have h_or: ⊢ (A ∨ ¬A) := MinimalDeduction.mp (MinimalDeduction.disj_intro_left A (¬A)) ha
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim (A ∨ ¬A)) h) h_or
  have h_or: ⊢ (A ∨ ¬A) := MinimalDeduction.mp (MinimalDeduction.disj_intro_right A (¬A)) hna
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim (A ∨ ¬A)) h) h_or

theorem double_neg_equiv (A : Formula α) : ⊢ (A ⇔ ¬¬A) := by
  have hfwd : ⊢ (A ⇒ ¬¬A) := by
    apply MinimalDeduction.deduction
    intro ha
    apply MinimalDeduction.mp (MinimalDeduction.neg_intro (¬A))
    apply MinimalDeduction.deduction
    intro hna
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim A) hna) ha
  have hbwd : ⊢ (¬¬A ⇒ A) := ClassicalDeduction.dne
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_intro A (¬¬A)) hfwd) hbwd

-- II. Classical De Morgan and Connective Equivalences
theorem disj_iff_not_conj_not (A B : Formula α) : ⊢ ((A ∨ B) ⇔ ¬(¬A ∧ ¬B)) := by
  have hfwd : ⊢ ((A ∨ B) ⇒ ¬(¬A ∧ ¬B)) := by
    apply MinimalDeduction.deduction
    intro hab
    apply MinimalDeduction.mp (MinimalDeduction.neg_intro (¬A ∧ ¬B))
    apply MinimalDeduction.deduction
    intro hnanb
    have hna : ⊢ ¬A := MinimalDeduction.mp (MinimalDeduction.conj_elim_left (¬A) (¬B)) hnanb
    have hnb : ⊢ ¬B := MinimalDeduction.mp (MinimalDeduction.conj_elim_right (¬A) (¬B)) hnanb
    have hna' : ⊢ A ⇒ ⊥ := by
      apply MinimalDeduction.deduction
      intro ha
      exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim A) hna) ha
    have hnb' : ⊢ B ⇒ ⊥ := by
      apply MinimalDeduction.deduction
      intro hb
      exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim B) hnb) hb
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.disj_elim A B ⊥) hna') hnb') hab
  have hbwd : ⊢ (¬(¬A ∧ ¬B) ⇒ (A ∨ B)) := by
    apply MinimalDeduction.deduction
    intro hnnanb
    apply MinimalDeduction.mp (proof_by_contradiction (A ∨ B))
    apply MinimalDeduction.deduction
    intro hnab
    have hna : ⊢ ¬A := by
      apply MinimalDeduction.mp (MinimalDeduction.neg_intro A)
      apply MinimalDeduction.deduction
      intro ha
      exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim (A ∨ B)) hnab) (MinimalDeduction.mp (MinimalDeduction.disj_intro_left A B) ha)
    have hnb : ⊢ ¬B := by
      apply MinimalDeduction.mp (MinimalDeduction.neg_intro B)
      apply MinimalDeduction.deduction
      intro hb
      exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim (A ∨ B)) hnab) (MinimalDeduction.mp (MinimalDeduction.disj_intro_right A B) hb)
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim (¬A ∧ ¬B)) hnnanb) (MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.conj_intro (¬A) (¬B)) hna) hnb)
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_intro (A ∨ B) (¬(¬A ∧ ¬B))) hfwd) hbwd

theorem conj_iff_not_disj_not (A B : Formula α) : ⊢ ((A ∧ B) ⇔ ¬(¬A ∨ ¬B)) := by
  have hfwd : ⊢ ((A ∧ B) ⇒ ¬(¬A ∨ ¬B)) := by
    apply MinimalDeduction.deduction
    intro hab
    apply MinimalDeduction.mp (MinimalDeduction.neg_intro (¬A ∨ ¬B))
    apply MinimalDeduction.deduction
    intro hnanb
    have ha : ⊢ A := MinimalDeduction.mp (MinimalDeduction.conj_elim_left A B) hab
    have hb : ⊢ B := MinimalDeduction.mp (MinimalDeduction.conj_elim_right A B) hab
    have hnna' : ⊢ ¬A ⇒ ⊥ := by
      apply MinimalDeduction.deduction
      intro hna
      exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim A) hna) ha
    have hnnb' : ⊢ ¬B ⇒ ⊥ := by
      apply MinimalDeduction.deduction
      intro hnb
      exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim B) hnb) hb
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.disj_elim (¬A) (¬B) ⊥) hnna') hnnb') hnanb
  have hbwd : ⊢ (¬(¬A ∨ ¬B) ⇒ (A ∧ B)) := by
    apply MinimalDeduction.deduction
    intro hnnanb
    have ha : ⊢ A := by
      apply MinimalDeduction.mp (proof_by_contradiction A)
      apply MinimalDeduction.deduction
      intro hna
      exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim (¬A ∨ ¬B)) hnnanb) (MinimalDeduction.mp (MinimalDeduction.disj_intro_left (¬A) (¬B)) hna)
    have hb : ⊢ B := by
      apply MinimalDeduction.mp (proof_by_contradiction B)
      apply MinimalDeduction.deduction
      intro hnb
      exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim (¬A ∨ ¬B)) hnnanb) (MinimalDeduction.mp (MinimalDeduction.disj_intro_right (¬A) (¬B)) hnb)
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.conj_intro A B) ha) hb
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_intro (A ∧ B) (¬(¬A ∨ ¬B))) hfwd) hbwd

theorem imp_iff_not_disj (A B : Formula α) : ⊢ ((A ⇒ B) ⇔ (¬A ∨ B)) := by
  have hfwd : ⊢ ((A ⇒ B) ⇒ (¬A ∨ B)) := by
    apply MinimalDeduction.deduction
    intro hnab
    apply MinimalDeduction.mp (proof_by_contradiction (¬A ∨ B))
    apply MinimalDeduction.deduction
    intro hnnab
    have hna : ⊢ ¬A := by
      apply MinimalDeduction.mp (MinimalDeduction.neg_intro A)
      apply MinimalDeduction.deduction
      intro ha
      have hb : ⊢ B := MinimalDeduction.mp hnab ha
      exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim (¬A ∨ B)) hnnab) (MinimalDeduction.mp (MinimalDeduction.disj_intro_right (¬A) B) hb)
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim (¬A ∨ B)) hnnab) (MinimalDeduction.mp (MinimalDeduction.disj_intro_left (¬A) B) hna)
  have hbwd : ⊢ ((¬A ∨ B) ⇒ (A ⇒ B)) := by
    apply MinimalDeduction.deduction
    intro hnab
    apply MinimalDeduction.deduction
    intro ha
    apply MinimalDeduction.mp (proof_by_contradiction B)
    apply MinimalDeduction.deduction
    intro hnb
    have hnna' : ⊢ ¬A ⇒ ⊥ := by
      apply MinimalDeduction.deduction
      intro hna
      exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim A) hna) ha
    have hnb' : ⊢ B ⇒ ⊥ := by
      apply MinimalDeduction.deduction
      intro hb
      exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim B) hnb) hb
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.disj_elim (¬A) B ⊥) hnna') hnb') hnab
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_intro (A ⇒ B) (¬A ∨ B)) hfwd) hbwd

theorem de_morgan_conj (A B : Formula α) : ⊢ (¬(A ∧ B) ⇔ (¬A ∨ ¬B)) := by
  have hfwd : ⊢ (¬(A ∧ B) ⇒ (¬A ∨ ¬B)) := by
    apply MinimalDeduction.deduction
    intro hnab
    apply MinimalDeduction.mp (proof_by_contradiction (¬A ∨ ¬B))
    apply MinimalDeduction.deduction
    intro hnnanb
    have ha : ⊢ A := by
      apply MinimalDeduction.mp (proof_by_contradiction A)
      apply MinimalDeduction.deduction
      intro hna
      exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim (¬A ∨ ¬B)) hnnanb) (MinimalDeduction.mp (MinimalDeduction.disj_intro_left (¬A) (¬B)) hna)
    have hb : ⊢ B := by
      apply MinimalDeduction.mp (proof_by_contradiction B)
      apply MinimalDeduction.deduction
      intro hnb
      exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim (¬A ∨ ¬B)) hnnanb) (MinimalDeduction.mp (MinimalDeduction.disj_intro_right (¬A) (¬B)) hnb)
    have hab : ⊢ (A ∧ B) := MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.conj_intro A B) ha) hb
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim (A ∧ B)) hnab) hab
  have hbwd : ⊢ ((¬A ∨ ¬B) ⇒ ¬(A ∧ B)) := disj_neg A B
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_intro (¬(A ∧ B)) (¬A ∨ ¬B)) hfwd) hbwd

-- III. Advanced Classical Equivalences
theorem neg_imp_iff_conj_neg (A B : Formula α) : ⊢ (¬(A ⇒ B) ⇔ (A ∧ ¬B)) := by
  have hfwd : ⊢ (¬(A ⇒ B) ⇒ (A ∧ ¬B)) := by
    apply MinimalDeduction.deduction
    intro hnab
    have ha : ⊢ A := by
      apply MinimalDeduction.mp (proof_by_contradiction A)
      apply MinimalDeduction.deduction
      intro hna
      have hab : ⊢ (A ⇒ B) := by
        apply MinimalDeduction.deduction
        intro ha
        exact MinimalDeduction.mp (ex_falso B) (MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim A) hna) ha)
      exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim (A ⇒ B)) hnab) hab
    have hnb : ⊢ ¬B := by
      apply MinimalDeduction.mp (MinimalDeduction.neg_intro B)
      apply MinimalDeduction.deduction
      intro hb
      have hab : ⊢ (A ⇒ B) := by
        apply MinimalDeduction.deduction
        intro ha
        exact hb
      exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim (A ⇒ B)) hnab) hab
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.conj_intro A (¬B)) ha) hnb
  have hbwd : ⊢ ((A ∧ ¬B) ⇒ ¬(A ⇒ B)) := by
    apply MinimalDeduction.deduction
    intro hanb
    have ha : ⊢ A := MinimalDeduction.mp (MinimalDeduction.conj_elim_left A (¬B)) hanb
    have hnb : ⊢ (¬B) := MinimalDeduction.mp (MinimalDeduction.conj_elim_right A (¬B)) hanb
    apply MinimalDeduction.mp (MinimalDeduction.neg_intro (A ⇒ B))
    apply MinimalDeduction.deduction
    intro hab
    have hb : ⊢ B := MinimalDeduction.mp hab ha
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim B) hnb) hb
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_intro (¬(A ⇒ B)) (A ∧ ¬B)) hfwd) hbwd

theorem contrapositive_equiv (A B : Formula α) : ⊢ ((A ⇒ B) ⇔ (¬B ⇒ ¬A)) := by
  have hfwd : ⊢ ((A ⇒ B) ⇒ (¬B ⇒ ¬A)) := imp_contrapositive A B
  have hbwd : ⊢ ((¬B ⇒ ¬A) ⇒ (A ⇒ B)) := by
    apply MinimalDeduction.deduction
    intro hnbna
    apply MinimalDeduction.deduction
    intro ha
    apply MinimalDeduction.mp (proof_by_contradiction B)
    apply MinimalDeduction.deduction
    intro hnb
    have hna : ⊢ ¬A := MinimalDeduction.mp hnbna hnb
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim A) hna) ha
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_intro (A ⇒ B) (¬B ⇒ ¬A)) hfwd) hbwd

theorem dist_imp_conj (A B C : Formula α) : ⊢ ((A ⇒ (B ∧ C)) ⇔ ((A ⇒ B) ∧ (A ⇒ C))) := by
  have hfwd : ⊢ ((A ⇒ (B ∧ C)) ⇒ ((A ⇒ B) ∧ (A ⇒ C))) := by
    apply MinimalDeduction.deduction
    intro h
    have hab : ⊢ A ⇒ B := by
      apply MinimalDeduction.deduction
      intro ha
      exact MinimalDeduction.mp (MinimalDeduction.conj_elim_left B C) (MinimalDeduction.mp h ha)
    have hac : ⊢ A ⇒ C := by
      apply MinimalDeduction.deduction
      intro ha
      exact MinimalDeduction.mp (MinimalDeduction.conj_elim_right B C) (MinimalDeduction.mp h ha)
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.conj_intro (A ⇒ B) (A ⇒ C)) hab) hac
  have hbwd : ⊢ (((A ⇒ B) ∧ (A ⇒ C)) ⇒ (A ⇒ (B ∧ C))) := by
    apply MinimalDeduction.deduction
    intro h
    apply MinimalDeduction.deduction
    intro ha
    have hb : ⊢ B := MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.conj_elim_left (A ⇒ B) (A ⇒ C)) h) ha
    have hc : ⊢ C := MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.conj_elim_right (A ⇒ B) (A ⇒ C)) h) ha
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.conj_intro (B) (C)) hb) hc
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_intro (A ⇒ (B ∧ C)) ((A ⇒ B) ∧ (A ⇒ C))) hfwd) hbwd

theorem peirce_law (A B : Formula α) : ⊢ (((A ⇒ B) ⇒ A) ⇒ A) := by
  apply MinimalDeduction.deduction
  intro hab_a
  apply MinimalDeduction.mp (proof_by_contradiction A)
  apply MinimalDeduction.deduction
  intro hna
  have hab : ⊢ (A ⇒ B) := by
    apply MinimalDeduction.deduction
    intro ha
    exact MinimalDeduction.mp (ex_falso B) (MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim A) hna) ha)
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim A) hna) (MinimalDeduction.mp hab_a hab)
