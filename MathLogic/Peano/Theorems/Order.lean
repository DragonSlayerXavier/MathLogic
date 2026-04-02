import MathLogic.Peano.Deduction
import MathLogic.Peano.Theorems.Addition

namespace Peano

variable {α : Type} [BEq α] [LawfulBEq α]
variable [MinimalFOLDeduction PeanoSignature α]
variable [ClassicalFOLDeduction PeanoSignature α]
variable [PeanoDeduction α]

def Le (k : α) (x y : Term PeanoSignature α) : Formula PeanoSignature α :=
  ∃' k, (x + V k) ≃ y

theorem zero_le (x k : α) :
  ⊢ Le k 0 (V x) := by
  sorry

theorem le_refl (x k : α) :
  ⊢ Le k (V x) (V x) := by
  sorry

theorem le_trans (x y z k1 k2 k3 : α) :
  ⊢ (Le k1 (V x) (V y) ∧ Le k2 (V y) (V z)) ⇒ Le k3 (V x) (V z) := by
  sorry

theorem le_antisymm (x y k1 k2 : α) :
  ⊢ (Le k1 (V x) (V y) ∧ Le k2 (V y) (V x)) ⇒ (V x ≃ V y) := by
  sorry

theorem le_total (x y k1 k2 : α) :
  ⊢ Le k1 (V x) (V y) ∨ Le k2 (V y) (V x) := by
  sorry

end Peano
