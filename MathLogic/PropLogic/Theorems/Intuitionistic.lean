import MathLogic.PropLogic.Syntax
import MathLogic.PropLogic.Deduction.Intuitionistic
--import MathLogic.PropLogic.Theorems.Minimal

open Formula
variable {α : Type} [IntuitionisticDeduction α]

-- I. Falsehood and Contradiction
theorem bot_iff_conj_neg (A : Formula α) : ⊢ (⊥ ⇔ (A ∧ ¬A)) := by sorry

-- II. Ex Falso Variations (Negation to Implication)
theorem neg_to_imp (A B : Formula α) : ⊢ (¬A ⇒ (A ⇒ B)) := by sorry

theorem neg_disj_to_imp (A B : Formula α) : ⊢ ((¬A ∨ B) ⇒ (A ⇒ B)) := by sorry

theorem disj_to_neg_imp (A B : Formula α) : ⊢ ((A ∨ B) ⇒ (¬A ⇒ B)) := by sorry

-- III. Double Negation and Implication
theorem neg_imp_to_double_neg (A B : Formula α) : ⊢ (¬(A ⇒ B) ⇒ ¬¬A) := by sorry

theorem double_neg_imp_equiv (A B : Formula α) : ⊢ (¬¬(A ⇒ B) ⇔ (¬¬A ⇒ ¬¬B)) := by sorry

-- IV. Bottom Elimination (Identity/Zero elements)
theorem disj_bot_iff_self (A : Formula α) : ⊢ ((A ∨ ⊥) ⇔ A) := by sorry

theorem conj_bot_iff_bot (A : Formula α) : ⊢ ((A ∧ ⊥) ⇔ ⊥) := by sorry
