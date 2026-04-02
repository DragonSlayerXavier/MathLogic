import MathLogic.Peano.Deduction

namespace Peano

variable {α : Type} [BEq α] [LawfulBEq α]
variable [MinimalFOLDeduction PeanoSignature α]
variable [ClassicalFOLDeduction PeanoSignature α]
variable [PeanoDeduction α]

theorem zero_add (x : α) :
  ⊢ (0 + V x) ≃ V x := by
  sorry

theorem succ_add (x y : α) :
  ⊢ (S' (V x) + V y) ≃ S' (V x + V y) := by
  sorry

theorem add_assoc (x y z : α) :
  ⊢ ((V x + V y) + V z) ≃ (V x + (V y + V z)) := by
  sorry

theorem add_comm (x y : α) :
  ⊢ (V x + V y) ≃ (V y + V x) := by
  sorry

theorem add_right_cancel (x y z : α) :
  ⊢ ((V x + V z) ≃ (V y + V z)) ⇒ (V x ≃ V y) := by
  sorry

end Peano
