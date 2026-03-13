import MathLogic.PropLogic.Syntax
import MathLogic.PropLogic.Deduction.Classical
--import MathLogic.PropLogic.Theorems.Minimal
--import MathLogic.PropLogic.Theorems.Intuitionistic

open Formula
variable {α : Type} [ClassicalDeduction α]

-- I. Fundamental Classical Principles
theorem proof_by_contradiction (A : Formula α) : ⊢ ((¬A ⇒ ⊥) ⇒ A) := by sorry

theorem ex_falso_classical (A : Formula α) : ⊢ (⊥ ⇒ A) := by sorry

theorem excluded_middle (A : Formula α) : ⊢ (A ∨ ¬A) := by sorry

theorem double_neg_equiv (A : Formula α) : ⊢ (A ⇔ ¬¬A) := by sorry

-- II. Classical De Morgan and Connective Equivalences
theorem disj_iff_not_conj_not (A B : Formula α) : ⊢ ((A ∨ B) ⇔ ¬(¬A ∧ ¬B)) := by sorry

theorem conj_iff_not_disj_not (A B : Formula α) : ⊢ ((A ∧ B) ⇔ ¬(¬A ∨ ¬B)) := by sorry

theorem imp_iff_not_disj (A B : Formula α) : ⊢ ((A ⇒ B) ⇔ (¬A ∨ B)) := by sorry

theorem de_morgan_conj (A B : Formula α) : ⊢ (¬(A ∧ B) ⇔ (¬A ∨ ¬B)) := by sorry

-- III. Advanced Classical Equivalences
theorem neg_imp_iff_conj_neg (A B : Formula α) : ⊢ (¬(A ⇒ B) ⇔ (A ∧ ¬B)) := by sorry

theorem contrapositive_equiv (A B : Formula α) : ⊢ ((A ⇒ B) ⇔ (¬B ⇒ ¬A)) := by sorry

theorem dist_imp_conj (A B C : Formula α) : ⊢ ((A ⇒ (B ∧ C)) ⇔ ((A ⇒ B) ∧ (A ⇒ C))) := by sorry

theorem peirce_law (A B : Formula α) : ⊢ (((A ⇒ B) ⇒ A) ⇒ A) := by sorry
