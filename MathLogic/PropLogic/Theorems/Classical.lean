import MathLogic.PropLogic.Syntax
import MathLogic.PropLogic.Deduction.Classical
--import MathLogic.PropLogic.Theorems.Minimal
--import MathLogic.PropLogic.Theorems.Intuitionistic

open Formula
variable {α : Type} [ClassicalDeduction α]

-- Helper for IFF notation
local infix:20 " ⇔ " => λ A B => (A ⇒ B) ∧ (B ⇒ A)

-- I. Fundamental Classical Principles
theorem proof_by_contradiction (A : Formula α) : ⊢ ((¬A ⇒ ⊥) ⇒ A) :=
  sorry

theorem ex_falso_classical (A : Formula α) : ⊢ (⊥ ⇒ A) :=
  sorry

theorem excluded_middle (A : Formula α) : ⊢ (A ∨ ¬A) :=
  sorry

theorem double_neg_equiv (A : Formula α) : ⊢ (A ⇔ ¬¬A) :=
  sorry

-- II. Classical De Morgan and Connective Equivalences
theorem disj_iff_not_conj_not (A B : Formula α) : ⊢ ((A ∨ B) ⇔ ¬(¬A ∧ ¬B)) :=
  sorry

theorem conj_iff_not_disj_not (A B : Formula α) : ⊢ ((A ∧ B) ⇔ ¬(¬A ∨ ¬B)) :=
  sorry

theorem imp_iff_not_disj (A B : Formula α) : ⊢ ((A ⇒ B) ⇔ (¬A ∨ B)) :=
  sorry

theorem de_morgan_conj (A B : Formula α) : ⊢ (¬(A ∧ B) ⇔ (¬A ∨ ¬B)) :=
  sorry

-- III. Advanced Classical Equivalences
theorem neg_imp_iff_conj_neg (A B : Formula α) : ⊢ (¬(A ⇒ B) ⇔ (A ∧ ¬B)) :=
  sorry

theorem contrapositive_equiv (A B : Formula α) : ⊢ ((A ⇒ B) ⇔ (¬B ⇒ ¬A)) :=
  sorry

theorem dist_imp_conj (A B C : Formula α) : ⊢ ((A ⇒ (B ∧ C)) ⇔ ((A ⇒ B) ∧ (A ⇒ C))) :=
  sorry

theorem peirce_law (A B : Formula α) : ⊢ (((A ⇒ B) ⇒ A) ⇒ A) :=
  sorry
