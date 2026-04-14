import MathLogic.PropLogic.Syntax
import MathLogic.PropLogic.Deduction.Intuitionistic
import MathLogic.PropLogic.Theorems.Minimal

open Formula
variable {α : Type} [IntuitionisticDeduction α]


theorem bot_iff_conj_neg (A : Formula α) : ⊢ (⊥ ⇔ (A ∧ ¬A)) := by
  have hfwd : ⊢ ⊥ ⇒ (A ∧ ¬A) := IntuitionisticDeduction.ex_falso
  have hbwd : ⊢ (A ∧ ¬A) ⇒ ⊥ := by
    apply MinimalDeduction.deduction
    intro ana
    have ha: ⊢ A := MinimalDeduction.mp (MinimalDeduction.conj_elim_left A (¬A)) ana
    have hna: ⊢ ¬A := MinimalDeduction.mp (MinimalDeduction.conj_elim_right A (¬A)) ana
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim A) hna) ha
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_intro ⊥ (A ∧ ¬A)) hfwd) hbwd


theorem neg_to_imp (A B : Formula α) : ⊢ (¬A ⇒ (A ⇒ B)) := by
  apply MinimalDeduction.deduction
  intro hna
  apply MinimalDeduction.deduction
  intro ha
  have hf: ⊢ ⊥ := MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim A) hna) ha
  exact MinimalDeduction.mp (IntuitionisticDeduction.ex_falso) hf

theorem neg_disj_to_imp (A B : Formula α) : ⊢ ((¬A ∨ B) ⇒ (A ⇒ B)) := by
  apply MinimalDeduction.deduction
  intro h
  apply MinimalDeduction.deduction
  intro ha
  have h_cases : ⊢ ((¬A ⇒ B) ⇒ ((B ⇒ B) ⇒ ((¬A ∨ B) ⇒ B))) := MinimalDeduction.disj_elim (¬A) B B
  have h_case_na : ⊢ (¬A ⇒ B) := by
    apply MinimalDeduction.deduction
    intro hna
    exact MinimalDeduction.mp (MinimalDeduction.mp (neg_to_imp A B) hna) ha
  have h_case_b : ⊢ (B ⇒ B) := self_imp B
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.mp h_cases h_case_na) h_case_b) h

theorem disj_to_neg_imp (A B : Formula α) : ⊢ ((A ∨ B) ⇒ (¬A ⇒ B)) := by
  apply MinimalDeduction.deduction
  intro hab
  apply MinimalDeduction.deduction
  intro hna
  have h_cases : ⊢ ((A ⇒ (¬A ⇒ B)) ⇒ ((B ⇒ (¬A ⇒ B)) ⇒ ((A ∨ B) ⇒ (¬A ⇒ B)))) := MinimalDeduction.disj_elim A B (¬A ⇒ B)
  have h_case_a : ⊢ (A ⇒ (¬A ⇒ B)) := by
    apply MinimalDeduction.deduction
    intro ha
    apply MinimalDeduction.deduction
    intro hna
    have hf: ⊢ ⊥ := MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim A) hna) ha
    exact MinimalDeduction.mp (IntuitionisticDeduction.ex_falso) hf
  have h_case_b : ⊢ (B ⇒ (¬A ⇒ B)) := by
    apply MinimalDeduction.deduction
    intro hb
    apply MinimalDeduction.deduction
    intro hna
    exact hb
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.mp h_cases h_case_a) h_case_b) hab) hna


theorem neg_imp_to_double_neg (A B : Formula α) : ⊢ (¬(A ⇒ B) ⇒ ¬¬A) := by
  apply MinimalDeduction.deduction
  intro hnab
  apply MinimalDeduction.mp (MinimalDeduction.neg_intro (¬A))
  apply MinimalDeduction.deduction
  intro hna
  have hab : ⊢ (A ⇒ B) := by
    apply MinimalDeduction.deduction
    intro ha
    have hf : ⊢ ⊥ := MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim A) hna) ha
    exact MinimalDeduction.mp (IntuitionisticDeduction.ex_falso) hf
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim (A ⇒ B)) hnab) hab

theorem double_neg_imp_equiv (A B : Formula α) : ⊢ (¬¬(A ⇒ B) ⇔ (¬¬A ⇒ ¬¬B)) := by
  have hfwd : ⊢ (¬¬(A ⇒ B) ⇒ (¬¬A ⇒ ¬¬B)) := by
    apply MinimalDeduction.deduction
    intro hnnab
    apply MinimalDeduction.deduction
    intro hnna
    apply MinimalDeduction.mp (MinimalDeduction.neg_intro (¬B))
    apply MinimalDeduction.deduction
    intro hnb
    have hnb_to_hnab : ⊢ (¬B ⇒ ¬(A ⇒ B)) := by
      apply MinimalDeduction.deduction
      intro hnb'
      apply MinimalDeduction.mp (MinimalDeduction.neg_intro (A ⇒ B))
      apply MinimalDeduction.deduction
      intro hab
      have hna : ⊢ ¬A := MinimalDeduction.mp (MinimalDeduction.mp (imp_contrapositive A B) hab) hnb'
      exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim (¬A)) hnna) hna
    have hnab : ⊢ ¬(A ⇒ B) := MinimalDeduction.mp hnb_to_hnab hnb
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim (¬(A ⇒ B))) hnnab) hnab
  have hbwd : ⊢ ((¬¬A ⇒ ¬¬B) ⇒ ¬¬(A ⇒ B)) := by
    apply MinimalDeduction.deduction
    intro hnnimp
    apply MinimalDeduction.mp (MinimalDeduction.neg_intro (¬(A ⇒ B)))
    apply MinimalDeduction.deduction
    intro hnab
    have hnna : ⊢ ¬¬A := MinimalDeduction.mp (neg_imp_to_double_neg A B) hnab
    have hnnb : ⊢ ¬¬B := MinimalDeduction.mp hnnimp hnna
    have hnb : ⊢ ¬B := MinimalDeduction.mp (imp_neg_elim A B) hnab
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.neg_elim (¬B)) hnnb) hnb
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_intro (¬¬(A ⇒ B)) (¬¬A ⇒ ¬¬B)) hfwd) hbwd


theorem disj_bot_iff_self (A : Formula α) : ⊢ ((A ∨ ⊥) ⇔ A) := by
  have hfwd : ⊢ ((A ∨ ⊥) ⇒ A) := by
    apply MinimalDeduction.deduction
    intro h
    have h_cases : ⊢ ((A ⇒ A) ⇒ ((⊥ ⇒ A) ⇒ ((A ∨ ⊥) ⇒ A))) := MinimalDeduction.disj_elim A ⊥ A
    have ha : ⊢ (A ⇒ A) := self_imp A
    have ha' : ⊢ (⊥ ⇒ A) := IntuitionisticDeduction.ex_falso
    exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.mp h_cases ha) ha') h
  have hbwd : ⊢ (A ⇒ (A ∨ ⊥)) := by
    apply MinimalDeduction.deduction
    intro ha
    exact MinimalDeduction.mp (MinimalDeduction.disj_intro_left A ⊥) ha
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_intro (A ∨ ⊥) A) hfwd) hbwd

theorem conj_bot_iff_bot (A : Formula α) : ⊢ ((A ∧ ⊥) ⇔ ⊥) := by
  have hfwd : ⊢ ((A ∧ ⊥) ⇒ ⊥) := by
    apply MinimalDeduction.deduction
    intro h
    exact MinimalDeduction.mp (MinimalDeduction.conj_elim_right A ⊥) h
  have hbwd : ⊢ (⊥ ⇒ (A ∧ ⊥)) := by
    apply MinimalDeduction.deduction
    intro h
    exact MinimalDeduction.mp (IntuitionisticDeduction.ex_falso) h
  exact MinimalDeduction.mp (MinimalDeduction.mp (MinimalDeduction.iff_intro (A ∧ ⊥) ⊥) hfwd) hbwd
