import MathLogic.PropLogic.Syntax
import MathLogic.PropLogic.Deduction.Minimal

open Formula
variable {α : Type} [MinimalDeduction α]

-- Helper for IFF in the object language
def iff (A B : Formula α) : Formula α := (A ⇒ B) ∧ (B ⇒ A)
infix:20 " ⇔ " => iff

-- I. Basic Implication and Syllogism
theorem self_imp (A : Formula α) : ⊢ A ⇒ A := sorry

theorem imp_trans (A B C : Formula α) : ⊢ (A ⇒ B) ⇒ ((B ⇒ C) ⇒ (A ⇒ C)) := sorry

-- II. Commutativity (Symmetry)
theorem conj_symm (A B : Formula α) : ⊢ (A ∧ B) ⇒ (B ∧ A) := sorry

theorem disj_symm (A B : Formula α) : ⊢ (A ∨ B) ⇒ (B ∨ A) := sorry

-- III. Associativity
theorem conj_assoc (A B C : Formula α) : ⊢ (A ∧ (B ∧ C)) ⇒ ((A ∧ B) ∧ C) := sorry

theorem disj_assoc (A B C : Formula α) : ⊢ (A ∨ (B ∨ C)) ⇒ ((A ∨ B) ∨ C) := sorry

-- IV. Distribution
theorem dist_conj_disj (A B C : Formula α) : ⊢ (A ∧ (B ∨ C)) ⇒ ((A ∧ B) ∨ (A ∧ C)) := sorry

theorem dist_disj_conj (A B C : Formula α) : ⊢ (A ∨ (B ∧ C)) ⇒ ((A ∨ B) ∧ (A ∨ C)) := sorry

-- V. IFF (Bi-implication)
theorem iff_conj (A B C : Formula α) : ⊢ (A ⇒ (B ⇒ C)) ⇔ ((A ∧ B) ⇒ C) := sorry

theorem iff_disj (A B C : Formula α) : ⊢ ((A ∨ B) ⇒ C) ⇔ ((A ⇒ C) ∧ (B ⇒ C)) := sorry

-- VI. Negation and Double Negation
theorem non_contradiction (A : Formula α) : ⊢ ¬(A ∧ ¬A) := sorry

theorem imp_neg_elim (A B : Formula α) : ⊢ ¬(A ⇒ B) ⇒ ¬B := sorry

theorem imp_contrapositive (A B : Formula α) : ⊢ (A ⇒ B) ⇒ (¬B ⇒ ¬A) := sorry

theorem double_neg_intro (A : Formula α) : ⊢ A ⇒ ¬¬A := sorry

theorem disj_neg (A B : Formula α) : ⊢ (¬A ∨ ¬B) ⇒ ¬(A ∧ B) := sorry

theorem de_morgan_disj (A B : Formula α) : ⊢ ¬(A ∨ B) ⇔ (¬A ∧ ¬B) := sorry

theorem triple_neg_equiv (A : Formula α) : ⊢ ¬A ⇔ ¬¬¬A := sorry

-- VII. Advanced Double Negation
theorem imp_neg_equiv_double_neg (A B : Formula α) : ⊢ (A ⇒ ¬B) ⇔ (¬¬A ⇒ ¬B) := sorry

theorem double_neg_disj_iff_not_conj_not (A B : Formula α) : ⊢ ¬¬(A ∨ B) ⇔ ¬(¬A ∧ ¬B) := sorry

theorem double_neg_imp_dist (A B : Formula α) : ⊢ ¬¬(A ⇒ B) ⇒ (¬¬A ⇒ ¬¬B) := sorry

theorem double_neg_conj_dist (A B : Formula α) : ⊢ ¬¬(A ∧ B) ⇔ (¬¬A ∧ ¬¬B) := sorry
