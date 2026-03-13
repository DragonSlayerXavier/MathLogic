import MathLogic.PropLogic.Syntax
import MathLogic.PropLogic.Deduction.Minimal

open Formula
variable {α : Type} [MinimalDeduction α]

-- I. Basic Implication and Syllogism
theorem self_imp (A : Formula α) : ⊢ A ⇒ A := by
  have h1 : ⊢ (A ⇒ (A ⇒ A)) := MinimalDeduction.aff_cons A A
  have h2 : ⊢ (A ⇒ ((A ⇒ A) ⇒ A)) := MinimalDeduction.aff_cons A (A ⇒ A)
  have h3 : ⊢ (A ⇒ ((A ⇒ A) ⇒ A)) ⇒ ((A ⇒ (A ⇒ A)) ⇒ (A ⇒ A)) := by
    apply MinimalDeduction.deduction
    intro h
    exact MinimalDeduction.mp (MinimalDeduction.dist_imp A (A ⇒ A) A) h
  have h4 : ⊢ (A ⇒ (A ⇒ A)) ⇒ (A ⇒ A) := MinimalDeduction.mp h3 h2
  exact MinimalDeduction.mp h4 h1

theorem imp_trans (A B C : Formula α) : ⊢ (A ⇒ B) ⇒ ((B ⇒ C) ⇒ (A ⇒ C)) := by
  apply MinimalDeduction.deduction
  intro hab
  apply MinimalDeduction.deduction
  intro hbc
  apply MinimalDeduction.deduction
  intro ha
  have hb : ⊢ B := MinimalDeduction.mp hab ha
  exact MinimalDeduction.mp hbc hb

-- II. Commutativity (Symmetry)
theorem conj_symm (A B : Formula α) : ⊢ (A ∧ B) ⇒ (B ∧ A) := by
  apply MinimalDeduction.deduction
  intro hab
  have ha : ⊢ A := MinimalDeduction.mp (MinimalDeduction.conj_elim_left A B) hab
  have hb : ⊢ B := MinimalDeduction.mp (MinimalDeduction.conj_elim_right A B) hab
  have h1 : ⊢ B ⇒ (A ⇒ (B ∧ A)) := MinimalDeduction.conj_intro B A
  have h2 : ⊢ A ⇒ (B ∧ A) := MinimalDeduction.mp h1 hb
  exact MinimalDeduction.mp h2 ha

theorem disj_symm (A B : Formula α) : ⊢ (A ∨ B) ⇒ (B ∨ A) := by
  apply MinimalDeduction.deduction
  intro hab
  have h1 : ⊢ (A ⇒ (B ∨ A)) := MinimalDeduction.disj_intro_right B A
  have h2 : ⊢ (B ⇒ (B ∨ A)) := MinimalDeduction.disj_intro_left B A
  have h3 : ⊢ ((A ⇒ (B ∨ A)) ⇒ ((B ⇒ (B ∨ A)) ⇒ ((A ∨ B) ⇒ (B ∨ A)))) := MinimalDeduction.disj_elim A B (B ∨ A)
  have h4 : ⊢ ((B ⇒ (B ∨ A)) ⇒ ((A ∨ B) ⇒ (B ∨ A))) := MinimalDeduction.mp h3 h1
  have h5 : ⊢ (A ∨ B) ⇒ (B ∨ A) := MinimalDeduction.mp h4 h2
  exact MinimalDeduction.mp h5 hab

-- III. Associativity
theorem conj_assoc (A B C : Formula α) : ⊢ (A ∧ (B ∧ C)) ⇒ ((A ∧ B) ∧ C) := by
  apply MinimalDeduction.deduction
  intro habc
  have ha : ⊢ A := MinimalDeduction.mp (MinimalDeduction.conj_elim_left A (B ∧ C)) habc
  have hbc : ⊢ (B ∧ C) := MinimalDeduction.mp (MinimalDeduction.conj_elim_right A (B ∧ C)) habc
  have hb : ⊢ B := MinimalDeduction.mp (MinimalDeduction.conj_elim_left B C) hbc
  have hc : ⊢ C := MinimalDeduction.mp (MinimalDeduction.conj_elim_right B C) hbc
  have h1 : ⊢ A ⇒ (B ⇒ (A ∧ B)) := MinimalDeduction.conj_intro A B
  have h2 : ⊢ B ⇒ (A ∧ B) := MinimalDeduction.mp h1 ha
  have hab : ⊢ A ∧ B := MinimalDeduction.mp h2 hb
  have h3 : ⊢ (A ∧ B) ⇒ (C ⇒ ((A ∧ B) ∧ C)) := MinimalDeduction.conj_intro (A ∧ B) C
  have h4 : ⊢ C ⇒ ((A ∧ B) ∧ C) := MinimalDeduction.mp h3 hab
  exact MinimalDeduction.mp h4 hc

theorem disj_assoc (A B C : Formula α) : ⊢ (A ∨ (B ∨ C)) ⇒ ((A ∨ B) ∨ C) := by
  apply MinimalDeduction.deduction
  intro habc
  have h1 : ⊢ (A ⇒ ((A ∨ B) ∨ C)) := by
    apply MinimalDeduction.deduction
    intro ha
    have hab : ⊢ A ∨ B := MinimalDeduction.mp (MinimalDeduction.disj_intro_left A B) ha
    exact MinimalDeduction.mp (MinimalDeduction.disj_intro_left (A ∨ B) C) hab
  have h2 : ⊢ ((B ∨ C) ⇒ ((A ∨ B) ∨ C)) := by
    apply MinimalDeduction.deduction
    intro hbc
    have h3 : ⊢ (B ⇒ ((A ∨ B) ∨ C)) := by
      apply MinimalDeduction.deduction
      intro hb
      have hab : ⊢ A ∨ B := MinimalDeduction.mp (MinimalDeduction.disj_intro_right A B) hb
      exact MinimalDeduction.mp (MinimalDeduction.disj_intro_left (A ∨ B) C) hab
    have h4 : ⊢ (C ⇒ ((A ∨ B) ∨ C)) := by
      apply MinimalDeduction.deduction
      intro hc
      exact MinimalDeduction.mp (MinimalDeduction.disj_intro_right (A ∨ B) C) hc
    have h5 := MinimalDeduction.disj_elim B C ((A ∨ B) ∨ C)
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.mp h5 h3) h4) hbc
  have h6 := MinimalDeduction.disj_elim A (B ∨ C) ((A ∨ B) ∨ C)
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.mp h6 h1) h2) habc

-- IV. Distribution
theorem dist_conj_disj (A B C : Formula α) : ⊢ (A ∧ (B ∨ C)) ⇒ ((A ∧ B) ∨ (A ∧ C)) := by
  apply MinimalDeduction.deduction
  intro habc
  have ha : ⊢ A := MinimalDeduction.mp (MinimalDeduction.conj_elim_left A (B ∨ C)) habc
  have hbc : ⊢ (B ∨ C) := MinimalDeduction.mp (MinimalDeduction.conj_elim_right A (B ∨ C)) habc
  have h1 : ⊢ (B ⇒ ((A ∧ B) ∨ (A ∧ C))) := by
    apply MinimalDeduction.deduction
    intro hb
    have hab : ⊢ A ∧ B := MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.conj_intro A B) ha) hb
    exact MinimalDeduction.mp (MinimalDeduction.disj_intro_left (A ∧ B) (A ∧ C)) hab
  have h2 : ⊢ (C ⇒ ((A ∧ B) ∨ (A ∧ C))) := by
    apply MinimalDeduction.deduction
    intro hc
    have hac : ⊢ A ∧ C := MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.conj_intro A C) ha) hc
    exact MinimalDeduction.mp (MinimalDeduction.disj_intro_right (A ∧ B) (A ∧ C)) hac
  have h3 := MinimalDeduction.disj_elim B C ((A ∧ B) ∨ (A ∧ C))
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.mp h3 h1) h2) hbc

theorem dist_disj_conj (A B C : Formula α) : ⊢ (A ∨ (B ∧ C)) ⇒ ((A ∨ B) ∧ (A ∨ C)) := by
  apply MinimalDeduction.deduction
  intro habc
  have h1 : ⊢ (A ⇒ ((A ∨ B) ∧ (A ∨ C))) := by
    apply MinimalDeduction.deduction
    intro ha
    have hab : ⊢ A ∨ B := MinimalDeduction.mp (MinimalDeduction.disj_intro_left A B) ha
    have hac : ⊢ A ∨ C := MinimalDeduction.mp (MinimalDeduction.disj_intro_left A C) ha
    have h2 : ⊢ (A ∨ B) ⇒ (A ∨ C) ⇒ ((A ∨ B) ∧ (A ∨ C)) := MinimalDeduction.conj_intro (A ∨ B) (A ∨ C)
    have h3 : ⊢ (A ∨ C) ⇒ ((A ∨ B) ∧ (A ∨ C)) := MinimalDeduction.mp h2 hab
    exact MinimalDeduction.mp h3 hac
  have h4 : ⊢ ((B ∧ C) ⇒ ((A ∨ B) ∧ (A ∨ C))) := by
    apply MinimalDeduction.deduction
    intro hbc
    have hb : ⊢ B := MinimalDeduction.mp (MinimalDeduction.conj_elim_left B C) hbc
    have hc : ⊢ C := MinimalDeduction.mp (MinimalDeduction.conj_elim_right B C) hbc
    have hab : ⊢ A ∨ B := MinimalDeduction.mp (MinimalDeduction.disj_intro_right A B) hb
    have hac : ⊢ A ∨ C := MinimalDeduction.mp (MinimalDeduction.disj_intro_right A C) hc
    have h2 := MinimalDeduction.conj_intro (A ∨ B) (A ∨ C)
    have h3 := MinimalDeduction.mp h2 hab
    exact MinimalDeduction.mp h3 hac
  have h5 := MinimalDeduction.disj_elim A (B ∧ C) ((A ∨ B) ∧ (A ∨ C))
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.mp h5 h1) h4) habc

-- V. IFF (Bi-implication)
theorem iff_conj (A B C : Formula α) : ⊢ (A ⇒ (B ⇒ C)) ⇔ ((A ∧ B) ⇒ C) := by
  have hfwd : ⊢ (A ⇒ (B ⇒ C)) ⇒ ((A ∧ B) ⇒ C) := by
    apply MinimalDeduction.deduction
    intro habc
    apply MinimalDeduction.deduction
    intro hab
    have ha : ⊢ A := MinimalDeduction.mp (MinimalDeduction.conj_elim_left A B) hab
    have hb : ⊢ B := MinimalDeduction.mp (MinimalDeduction.conj_elim_right A B) hab
    have hbc : ⊢ B ⇒ C := MinimalDeduction.mp habc ha
    exact MinimalDeduction.mp hbc hb
  have hbwd : ⊢ ((A ∧ B) ⇒ C) ⇒ (A ⇒ (B ⇒ C)) := by
    apply MinimalDeduction.deduction
    intro habc
    apply MinimalDeduction.deduction
    intro ha
    apply MinimalDeduction.deduction
    intro hb
    have hab : ⊢ A ∧ B := MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.conj_intro A B) ha) hb
    exact MinimalDeduction.mp habc hab
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_intro (A ⇒ (B ⇒ C)) ((A ∧ B) ⇒ C)) hfwd) hbwd

theorem iff_disj (A B C : Formula α) : ⊢ ((A ∨ B) ⇒ C) ⇔ ((A ⇒ C) ∧ (B ⇒ C)) := by
  have hfwd : ⊢ ((A ∨ B) ⇒ C) ⇒ ((A ⇒ C) ∧ (B ⇒ C)) := by
    apply MinimalDeduction.deduction
    intro habc
    have hac : ⊢ A ⇒ C := by
      apply MinimalDeduction.deduction
      intro ha
      have hab : ⊢ A ∨ B := MinimalDeduction.mp (MinimalDeduction.disj_intro_left A B) ha
      exact MinimalDeduction.mp habc hab
    have hbc : ⊢ B ⇒ C := by
      apply MinimalDeduction.deduction
      intro hb
      have hab : ⊢ A ∨ B := MinimalDeduction.mp (MinimalDeduction.disj_intro_right A B) hb
      exact MinimalDeduction.mp habc hab
    have h1 := MinimalDeduction.conj_intro (A ⇒ C) (B ⇒ C)
    have h2 := MinimalDeduction.mp h1 hac
    exact MinimalDeduction.mp h2 hbc
  have hbwd : ⊢ ((A ⇒ C) ∧ (B ⇒ C)) ⇒ ((A ∨ B) ⇒ C) := by
    apply MinimalDeduction.deduction
    intro habc
    have hac : ⊢ A ⇒ C := MinimalDeduction.mp (MinimalDeduction.conj_elim_left (A ⇒ C) (B ⇒ C)) habc
    have hbc : ⊢ B ⇒ C := MinimalDeduction.mp (MinimalDeduction.conj_elim_right (A ⇒ C) (B ⇒ C)) habc
    apply MinimalDeduction.deduction
    intro hab
    have h1 := MinimalDeduction.disj_elim A B C
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.mp h1 hac) hbc) hab
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_intro ((A ∨ B) ⇒ C) ((A ⇒ C) ∧ (B ⇒ C))) hfwd) hbwd

-- VI. Negation and Double Negation
theorem non_contradiction (A : Formula α) : ⊢ ¬(A ∧ ¬A) := by
  apply MinimalDeduction.mp (MinimalDeduction.neg_intro (A ∧ ¬A))
  apply MinimalDeduction.deduction
  intro h
  have ha : ⊢ A := MinimalDeduction.mp (MinimalDeduction.conj_elim_left A (¬A)) h
  have hna : ⊢ ¬A := MinimalDeduction.mp (MinimalDeduction.conj_elim_right A (¬A)) h
  have h1 : ⊢ A ⇒ ⊥ := MinimalDeduction.mp (MinimalDeduction.neg_elim A) hna
  exact MinimalDeduction.mp h1 ha

theorem imp_neg_elim (A B : Formula α) : ⊢ ¬(A ⇒ B) ⇒ ¬B := by
  apply MinimalDeduction.deduction
  intro hnab
  apply MinimalDeduction.mp (MinimalDeduction.neg_intro B)
  apply MinimalDeduction.deduction
  intro hb
  have hab : ⊢ A ⇒ B := by
    apply MinimalDeduction.deduction
    intro ha
    exact hb
  have hnab' := MinimalDeduction.mp (MinimalDeduction.neg_elim (A ⇒ B)) hnab
  exact MinimalDeduction.mp hnab' hab

theorem imp_contrapositive (A B : Formula α) : ⊢ (A ⇒ B) ⇒ (¬B ⇒ ¬A) := by
  apply MinimalDeduction.deduction
  intro hab
  apply MinimalDeduction.deduction
  intro hnb
  apply MinimalDeduction.mp (MinimalDeduction.neg_intro A)
  apply MinimalDeduction.deduction
  intro ha
  have hb : ⊢ B := MinimalDeduction.mp hab ha
  have hnb' := MinimalDeduction.mp (MinimalDeduction.neg_elim B) hnb
  exact MinimalDeduction.mp hnb' hb

theorem double_neg_intro (A : Formula α) : ⊢ A ⇒ ¬¬A := by
  apply MinimalDeduction.deduction
  intro ha
  apply MinimalDeduction.mp (MinimalDeduction.neg_intro (¬A))
  apply MinimalDeduction.deduction
  intro hna
  have hna' := MinimalDeduction.mp (MinimalDeduction.neg_elim A) hna
  exact MinimalDeduction.mp hna' ha

theorem disj_neg (A B : Formula α) : ⊢ ((¬A) ∨ ¬B) ⇒ ¬(A ∧ B) := by
  apply MinimalDeduction.deduction
  intro h
  apply MinimalDeduction.mp (MinimalDeduction.neg_intro (A ∧ B))
  apply MinimalDeduction.deduction
  intro hab
  have ha : ⊢ A := MinimalDeduction.mp (MinimalDeduction.conj_elim_left A B) hab
  have hb : ⊢ B := MinimalDeduction.mp (MinimalDeduction.conj_elim_right A B) hab
  have h1 : ⊢ (¬A ⇒ ⊥) := by
    apply MinimalDeduction.deduction
    intro hna
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim A) hna) ha
  have h2 : ⊢ (¬B ⇒ ⊥) := by
    apply MinimalDeduction.deduction
    intro hnb
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim B) hnb) hb
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.disj_elim (¬A) (¬B) ⊥) h1) h2) h

theorem de_morgan_disj (A B : Formula α) : ⊢ ¬(A ∨ B) ⇔ (¬A ∧ ¬B) := by
  have hfwd : ⊢ ¬(A ∨ B) ⇒ (¬A ∧ ¬B) := by
    apply MinimalDeduction.deduction
    intro h
    have hna: ⊢ ¬A := by
      apply MinimalDeduction.mp (MinimalDeduction.neg_intro A)
      apply MinimalDeduction.deduction
      intro ha
      have hab : ⊢ A ∨ B := MinimalDeduction.mp (MinimalDeduction.disj_intro_left A B) ha
      have hnab := MinimalDeduction.mp (MinimalDeduction.neg_elim (A ∨ B)) h
      exact MinimalDeduction.mp hnab hab
    have hnb: ⊢ ¬B := by
      apply MinimalDeduction.mp (MinimalDeduction.neg_intro B)
      apply MinimalDeduction.deduction
      intro hb
      have hab : ⊢ A ∨ B := MinimalDeduction.mp (MinimalDeduction.disj_intro_right A B) hb
      have hnab := MinimalDeduction.mp (MinimalDeduction.neg_elim (A ∨ B)) h
      exact MinimalDeduction.mp hnab hab
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.conj_intro (¬A) (¬B)) hna) hnb
  have hbwd : ⊢ (¬A ∧ ¬B) ⇒ ¬(A ∨ B) := by
    apply MinimalDeduction.deduction
    intro h
    apply MinimalDeduction.mp (MinimalDeduction.neg_intro (A ∨ B))
    apply MinimalDeduction.deduction
    intro hab
    have hna : ⊢ ¬A := MinimalDeduction.mp (MinimalDeduction.conj_elim_left (¬A) (¬B)) h
    have hnb : ⊢ ¬B := MinimalDeduction.mp (MinimalDeduction.conj_elim_right (¬A) (¬B)) h
    have h1 : ⊢ (A ⇒ ⊥) := MinimalDeduction.mp (MinimalDeduction.neg_elim A) hna
    have h2 : ⊢ (B ⇒ ⊥) := MinimalDeduction.mp (MinimalDeduction.neg_elim B) hnb
    have h3 : ⊢ (A ⇒ ⊥) ⇒ ((B ⇒ ⊥) ⇒ ((A ∨ B) ⇒ ⊥)) := MinimalDeduction.disj_elim A B ⊥
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.mp h3 h1) h2) hab
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_intro (¬(A ∨ B)) (¬A ∧ ¬B)) hfwd) hbwd

theorem triple_neg_equiv (A : Formula α) : ⊢ ¬A ⇔ ¬¬¬A := by
  have hfwd : ⊢ ¬A ⇒ ¬¬¬A := double_neg_intro (¬A)
  have hbwd : ⊢ ¬¬¬A ⇒ ¬A := by
    apply MinimalDeduction.deduction
    intro hnnna
    apply MinimalDeduction.mp (MinimalDeduction.neg_intro A)
    apply MinimalDeduction.deduction
    intro ha
    have hnna : ⊢ ¬¬A := MinimalDeduction.mp (double_neg_intro A) ha
    have hnnna' := MinimalDeduction.mp (MinimalDeduction.neg_elim (¬¬A)) hnnna
    exact MinimalDeduction.mp hnnna' hnna
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_intro (¬A) (¬¬¬A)) hfwd) hbwd

-- VII. Advanced Double Negation
theorem imp_neg_equiv_double_neg (A B : Formula α) : ⊢ (A ⇒ ¬B) ⇔ (¬¬A ⇒ ¬B) := by
  have hfwd : ⊢ (A ⇒ ¬B) ⇒ (¬¬A ⇒ ¬B) := by
    apply MinimalDeduction.deduction
    intro hanb
    apply MinimalDeduction.deduction
    intro hnna
    apply MinimalDeduction.mp (MinimalDeduction.neg_intro B)
    apply MinimalDeduction.deduction
    intro hb
    have hna : ⊢ ¬A := by
      apply MinimalDeduction.mp (MinimalDeduction.neg_intro A)
      apply MinimalDeduction.deduction
      intro ha
      have hnb : ⊢ ¬B := MinimalDeduction.mp hanb ha
      exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim B) hnb) hb
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim (¬A)) hnna) hna
  have hbwd : ⊢ (¬¬A ⇒ ¬B) ⇒ (A ⇒ ¬B) := by
    apply MinimalDeduction.deduction
    intro hnnanb
    apply MinimalDeduction.deduction
    intro ha
    have hnna : ⊢ ¬¬A := MinimalDeduction.mp (double_neg_intro A) ha
    exact MinimalDeduction.mp hnnanb hnna
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_intro (A ⇒ ¬B) (¬¬A ⇒ ¬B)) hfwd) hbwd

theorem double_neg_disj_iff_not_conj_not (A B : Formula α) : ⊢ ¬¬(A ∨ B) ⇔ ¬(¬A ∧ ¬B) := by
  have h_dm := de_morgan_disj A B
  have hfwd : ⊢ ¬¬(A ∨ B) ⇒ ¬(¬A ∧ ¬B) := by
    apply MinimalDeduction.deduction
    intro hnnab
    apply MinimalDeduction.mp (MinimalDeduction.neg_intro (¬A ∧ ¬B))
    apply MinimalDeduction.deduction
    intro hnanb
    have hnab : ⊢ ¬(A ∨ B) := MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_elim_right (¬(A ∨ B)) (¬A ∧ ¬B)) h_dm) hnanb
    have hnab' := MinimalDeduction.mp (MinimalDeduction.neg_elim (¬(A ∨ B))) hnnab
    exact MinimalDeduction.mp hnab' hnab
  have hbwd : ⊢ ¬(¬A ∧ ¬B) ⇒ ¬¬(A ∨ B) := by
    apply MinimalDeduction.deduction
    intro hnnanb
    apply MinimalDeduction.mp (MinimalDeduction.neg_intro (¬(A ∨ B)))
    apply MinimalDeduction.deduction
    intro hnab
    have hnanb : ⊢ ¬A ∧ ¬B := MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_elim_left (¬(A ∨ B)) (¬A ∧ ¬B)) h_dm) hnab
    have hnanb' := MinimalDeduction.mp (MinimalDeduction.neg_elim (¬A ∧ ¬B)) hnnanb
    exact MinimalDeduction.mp hnanb' hnanb
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_intro (¬¬(A ∨ B)) (¬(¬A ∧ ¬B))) hfwd) hbwd

theorem double_neg_imp_dist (A B : Formula α) : ⊢ ¬¬(A ⇒ B) ⇒ (¬¬A ⇒ ¬¬B) := by
  apply MinimalDeduction.deduction
  intro hnnab
  apply MinimalDeduction.deduction
  intro hnna
  apply MinimalDeduction.mp (MinimalDeduction.neg_intro (¬B))
  apply MinimalDeduction.deduction
  intro hnb
  have hnab : ⊢ ¬(A ⇒ B) := by
    apply MinimalDeduction.mp (MinimalDeduction.neg_intro (A ⇒ B))
    apply MinimalDeduction.deduction
    intro hab
    have hna : ⊢ ¬A := by
      apply MinimalDeduction.mp (MinimalDeduction.neg_intro A)
      apply MinimalDeduction.deduction
      intro ha
      have hb : ⊢ B := MinimalDeduction.mp hab ha
      have hnb' := MinimalDeduction.mp (MinimalDeduction.neg_elim B) hnb
      exact MinimalDeduction.mp hnb' hb
    have hnna' := MinimalDeduction.mp (MinimalDeduction.neg_elim (¬A)) hnna
    exact MinimalDeduction.mp hnna' hna
  have hnab' := MinimalDeduction.mp (MinimalDeduction.neg_elim (¬(A ⇒ B))) hnnab
  exact MinimalDeduction.mp hnab' hnab

theorem double_neg_conj_dist (A B : Formula α) : ⊢ ¬¬(A ∧ B) ⇔ (¬¬A ∧ ¬¬B) := by
  have hfwd : ⊢ ¬¬(A ∧ B) ⇒ (¬¬A ∧ ¬¬B) := by
    apply MinimalDeduction.deduction
    intro hnnab
    have hnna : ⊢ ¬¬A := by
      apply MinimalDeduction.mp (MinimalDeduction.neg_intro (¬A))
      apply MinimalDeduction.deduction
      intro hna
      have hna' := MinimalDeduction.mp (MinimalDeduction.neg_elim A) hna
      have hnnab' := MinimalDeduction.mp (MinimalDeduction.neg_elim (¬(A ∧ B))) hnnab
      have hnab : ⊢ ¬(A ∧ B) := by
        apply MinimalDeduction.mp (MinimalDeduction.neg_intro (A ∧ B))
        apply MinimalDeduction.deduction
        intro hab
        exact MinimalDeduction.mp hna' (MinimalDeduction.mp (MinimalDeduction.conj_elim_left A B) hab)
      exact MinimalDeduction.mp hnnab' hnab
    have hnnb : ⊢ ¬¬B := by
      apply MinimalDeduction.mp (MinimalDeduction.neg_intro (¬B))
      apply MinimalDeduction.deduction
      intro hnb
      have hnb' := MinimalDeduction.mp (MinimalDeduction.neg_elim B) hnb
      have hnnab' := MinimalDeduction.mp (MinimalDeduction.neg_elim (¬(A ∧ B))) hnnab
      have hnab : ⊢ ¬(A ∧ B) := by
        apply MinimalDeduction.mp (MinimalDeduction.neg_intro (A ∧ B))
        apply MinimalDeduction.deduction
        intro hab
        exact MinimalDeduction.mp hnb' (MinimalDeduction.mp (MinimalDeduction.conj_elim_right A B) hab)
      exact MinimalDeduction.mp hnnab' hnab
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.conj_intro (¬¬A) (¬¬B)) hnna) hnnb
  have hbwd : ⊢ (¬¬A ∧ ¬¬B) ⇒ ¬¬(A ∧ B) := by
    apply MinimalDeduction.deduction
    intro hnnannb
    have hnna : ⊢ ¬¬A := MinimalDeduction.mp (MinimalDeduction.conj_elim_left (¬¬A) (¬¬B)) hnnannb
    have hnnb : ⊢ ¬¬B := MinimalDeduction.mp (MinimalDeduction.conj_elim_right (¬¬A) (¬¬B)) hnnannb
    apply MinimalDeduction.mp (MinimalDeduction.neg_intro (¬(A ∧ B)))
    apply MinimalDeduction.deduction
    intro hnab
    have hna : ⊢ ¬A := by
      apply MinimalDeduction.mp (MinimalDeduction.neg_intro A)
      apply MinimalDeduction.deduction
      intro ha
      have hnb : ⊢ ¬B := by
        apply MinimalDeduction.mp (MinimalDeduction.neg_intro B)
        apply MinimalDeduction.deduction
        intro hb
        have hnab' := MinimalDeduction.mp (MinimalDeduction.neg_elim (A ∧ B)) hnab
        exact MinimalDeduction.mp hnab' (MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.conj_intro A B) ha) hb)
      have hnnb' := MinimalDeduction.mp (MinimalDeduction.neg_elim (¬B)) hnnb
      exact MinimalDeduction.mp hnnb' hnb
    have hnna' := MinimalDeduction.mp (MinimalDeduction.neg_elim (¬A)) hnna
    exact MinimalDeduction.mp hnna' hna
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_intro (¬¬(A ∧ B)) (¬¬A ∧ ¬¬B)) hfwd) hbwd
