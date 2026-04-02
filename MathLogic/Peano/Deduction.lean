import MathLogic.Peano.Syntax
import MathLogic.FOL.Deduction.Classical
import MathLogic.FOL.Deduction.Equality

def V {α : Type} (x : α) : Term PeanoSignature α := .var x

class PeanoDeduction (α : Type) [BEq α] [LawfulBEq α] [ClassicalFOLDeduction PeanoSignature α] where
  zero_not_succ : ∀ (x : α),
    ⊢ ¬(S' (V x) ≃ 0)

  succ_inj : ∀ (x y : α),
    ⊢ (S' (V x) ≃ S' (V y)) ⇒ (V x ≃ V y)

  add_zero : ∀ (x : α),
    ⊢ (V x + 0) ≃ V x

  add_succ : ∀ (x y : α),
    ⊢ (V x + S' (V y)) ≃ S' (V x + V y)

  mul_zero : ∀ (x : α),
    ⊢ (V x * 0) ≃ 0

  mul_succ : ∀ (x y : α),
    ⊢ (V x * S' (V y)) ≃ (V x * V y) + V x

  induction : ∀ (p : Formula PeanoSignature α) (x : α),
    ⊢ p⟦x := 0⟧ ⇒ ((∀' x, p ⇒ p⟦x := S' (V x)⟧) ⇒ ∀' x, p)

class PeanoEquality (α : Type) [BEq α] [LawfulBEq α] [MinimalFOLDeduction PeanoSignature α] [EqualityDeduction PeanoSignature α PeanoPred.eq] where
  cong_succ : ∀ (t1 t2 : Term PeanoSignature α),
    ⊢ (t1 ≃ t2) ⇒ (S' t1 ≃ S' t2)

  cong_add : ∀ (t1 t2 t3 t4 : Term PeanoSignature α),
    ⊢ (t1 ≃ t2) ⇒ ((t3 ≃ t4) ⇒ (t1 + t3 ≃ t2 + t4))

  cong_mul : ∀ (t1 t2 t3 t4 : Term PeanoSignature α),
    ⊢ (t1 ≃ t2) ⇒ ((t3 ≃ t4) ⇒ (t1 * t3 ≃ t2 * t4))
