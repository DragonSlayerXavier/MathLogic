import MathLogic.FOL.Syntax
import MathLogic.FOL.Deduction.Classical
import MathLogic.FOL.Theorems.Minimal
import MathLogic.FOL.Theorems.Intuitionistic

variable {S : Signature} {α : Type} [BEq α] [ClassicalFOLDeduction S α]

theorem ex_falso {p : Formula S α} : ⊢ ⊥ ⇒ p := sorry

-- Reductio ad absurdum
theorem proof_by_contradiction {p : Formula S α} :
  ⊢ (¬p ⇒ ⊥) ⇒ p := sorry

-- The classical De Morgan equivalence for quantifiers
theorem ex_not_iff_not_all {p : Formula S α} (x : α) :
  ⊢ (∃' x, ¬p) ⇔ ¬∀' x, p := sorry
