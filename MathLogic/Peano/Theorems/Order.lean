import MathLogic.Peano.Deduction
import MathLogic.Peano.Theorems.Addition

namespace Peano

variable {α : Type} [BEq α] [LawfulBEq α]
variable [ClassicalFOLDeduction PeanoSignature α]
variable [EqualityDeduction PeanoSignature α PeanoPred.eq]
variable [PeanoDeduction α]

def Le (k : α) (x y : Term PeanoSignature α) : Formula PeanoSignature α :=
  ∃' k, (x + V k) ≃ y

theorem zero_le (x k : α) [PeanoEquality α] [VariableSupply α] :
  ⊢ Le k 0 (V x) := by
  unfold Le
  let body : Formula PeanoSignature α := (0 + V k) ≃ V x
  let witness := V x

  have h_sub : body⟦k := witness⟧ = (0 + V x ≃ V x) := by
    unfold body substF peanoEq
    simp only [List.map_cons, List.map_nil, Formula.pred.injEq, List.cons.injEq, and_true, true_and]
    unfold substT
    simp only [List.map, beq_iff_eq, witness]
    apply And.intro
    · unfold substT
      simp [List.map]
      unfold V
      dsimp
      simp only [BEq.rfl, ↓reduceIte]
      rfl
    · unfold substT V
      simp only [beq_iff_eq, ite_self]

  let h_za := zero_add x
  rw [← h_sub] at h_za

  have h_free : isFreeFor witness k body := by
    unfold isFreeFor
    rfl

  let ax := MinimalFOLDeduction.ex_intro k witness h_free
  exact MinimalFOLDeduction.mp ax h_za

theorem le_refl (x k : α) [PeanoEquality α] [VariableSupply α] :
  ⊢ Le k (V x) (V x) := by
  unfold Le
  let body : Formula PeanoSignature α := (V x + V k) ≃ V x
  let witness : Term PeanoSignature α := 0
  let t := if k == x then (0 : Term PeanoSignature α) else V x

  have h_sub : body⟦k := witness⟧ = (t + 0 ≃ t) := by
    unfold body substF peanoEq t
    simp only [List.map_cons, List.map_nil, Formula.pred.injEq, List.cons.injEq, and_true, true_and]
    unfold substT
    simp only [List.map, witness]
    apply And.intro
    · unfold substT V
      simp only [beq_iff_eq, BEq.rfl, ↓reduceIte]
      rfl
    · rfl

  let h := PeanoDeduction.add_zero t
  rw [← h_sub] at h

  have h_free : isFreeFor witness k body := by
    unfold isFreeFor
    rfl

  let ax := MinimalFOLDeduction.ex_intro k witness h_free
  exact MinimalFOLDeduction.mp ax h

theorem le_trans (x y z k1 k2 k3 : α) [PeanoEquality α] [VariableSupply α] [LawfulBEq α]
  (h_dist : [x, y, z, k1, k2, k3].Pairwise (· ≠ ·)) :
  ⊢ (Le k1 (V x) (V y) ∧ Le k2 (V y) (V z)) ⇒ Le k3 (V x) (V z) := by
  sorry

theorem le_antisymm (x y k1 k2 : α) [PeanoEquality α] [VariableSupply α]
  (h_dist : [x, y, k1, k2].Pairwise (· ≠ ·)) :
  ⊢ (Le k1 (V x) (V y) ∧ Le k2 (V y) (V x)) ⇒ (V x ≃ V y) := by
  sorry

theorem le_total (x y k1 k2 : α) [PeanoEquality α] [VariableSupply α]
  (h_dist : [x, y, k1, k2].Pairwise (· ≠ ·)) :
  ⊢ Le k1 (V x) (V y) ∨ Le k2 (V y) (V x) := by
  sorry

end Peano
