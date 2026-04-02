import MathLogic.Peano.Deduction
import MathLogic.Peano.Theorems.Addition

namespace Peano

variable {α : Type} [BEq α] [LawfulBEq α]
variable [MinimalFOLDeduction PeanoSignature α]
variable [ClassicalFOLDeduction PeanoSignature α]
variable [PeanoDeduction α]

theorem zero_mul (x : α) :
  ⊢ (0 * V x) ≃ 0 := by
  sorry

theorem succ_mul (x y : α) :
  ⊢ (S' (V x) * V y) ≃ ((V x * V y) + V y) := by
  sorry

theorem add_mul (x y z : α) :
  ⊢ ((V x + V y) * V z) ≃ ((V x * V z) + (V y * V z)) := by
  sorry

theorem mul_add (x y z : α) :
  ⊢ (V x * (V y + V z)) ≃ ((V x * V y) + (V x * V z)) := by
  sorry

theorem mul_assoc (x y z : α) :
  ⊢ ((V x * V y) * V z) ≃ (V x * (V y * V z)) := by
  sorry

theorem mul_comm (x y : α) :
  ⊢ (V x * V y) ≃ (V y * V x) := by
  sorry

end Peano
