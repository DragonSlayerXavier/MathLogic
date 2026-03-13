import MathLogic.PropLogic.Syntax
import MathLogic.PropLogic.Deduction.Intuitionistic
--import MathLogic.PropLogic.Theorems.Minimal

open Formula
variable {α : Type} [IntuitionisticDeduction α]

-- Helper for IFF notation
local infix:20 " ⇔ " => λ A B => (A ⇒ B) ∧ (B ⇒ A)

-- I. Falsehood and Contradiction
theorem bot_iff_conj_neg (A : Formula α) : ⊢ (⊥ ⇔ (A ∧ ¬A)) :=
  sorry

-- II. Ex Falso Variations (Negation to Implication)
theorem neg_to_imp (A B : Formula α) : ⊢ (¬A ⇒ (A ⇒ B)) :=
  sorry

theorem neg_disj_to_imp (A B : Formula α) : ⊢ ((¬A ∨ B) ⇒ (A ⇒ B)) :=
  sorry

theorem disj_to_neg_imp (A B : Formula α) : ⊢ ((A ∨ B) ⇒ (¬A ⇒ B)) :=
  sorry

-- III. Double Negation and Implication
theorem neg_imp_to_double_neg (A B : Formula α) : ⊢ (¬(A ⇒ B) ⇒ ¬¬A) :=
  sorry

theorem double_neg_imp_equiv (A B : Formula α) : ⊢ (¬¬(A ⇒ B) ⇔ (¬¬A ⇒ ¬¬B)) :=
  sorry

-- IV. Bottom Elimination (Identity/Zero elements)
theorem disj_bot_iff_self (A : Formula α) : ⊢ ((A ∨ ⊥) ⇔ A) :=
  sorry

theorem conj_bot_iff_bot (A : Formula α) : ⊢ ((A ∧ ⊥) ⇔ ⊥) :=
  sorry
