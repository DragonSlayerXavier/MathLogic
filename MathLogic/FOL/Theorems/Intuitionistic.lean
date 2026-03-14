import MathLogic.FOL.Syntax
import MathLogic.FOL.Deduction.Intuitionistic
import MathLogic.FOL.Theorems.Minimal

variable {S : Signature} {α : Type} [BEq α] [IntuitionisticFoldeduction S α]

-- The forward direction of one of the De Morgan laws for quantifiers
theorem all_iff_not_ex_not {p : Formula S α} (x : α) :
  ⊢ (∀' x, p) ⇔ ¬∃' x, ¬p := sorry

-- Distributing existence over implication when x is not free in B
theorem ex_imp_dist_left_iff {p q : Formula S α} (x : α) :
  isFreeIn x q = false → ⊢ (∃' x, p ⇒ q) ⇔ (∀' x, p) ⇒ q := sorry

-- Distributing existence over implication when x is not free in A
theorem ex_imp_dist_right_iff {p q : Formula S α} (x : α) :
  isFreeIn x p = false → ⊢ (∃' x, p ⇒ q) ⇔ p ⇒ ∃' x, q := sorry
