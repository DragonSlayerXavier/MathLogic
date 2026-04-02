import MathLogic.Peano.Syntax
import MathLogic.FOL.Deduction.Classical
import MathLogic.FOL.Deduction.Equality

def V {α : Type} (x : α) : Term PeanoSignature α := .var x

class PeanoEquality (α : Type) [BEq α] [LawfulBEq α] [MinimalFOLDeduction PeanoSignature α] [EqualityDeduction PeanoSignature α PeanoPred.eq] where
  cong_succ : ∀ (t1 t2 : Term PeanoSignature α),
    ⊢ (t1 ≃ t2) ⇒ (S' t1 ≃ S' t2)

  cong_add : ∀ (t1 t2 t3 t4 : Term PeanoSignature α),
    ⊢ (t1 ≃ t2) ⇒ ((t3 ≃ t4) ⇒ (t1 + t3 ≃ t2 + t4))

  cong_mul : ∀ (t1 t2 t3 t4 : Term PeanoSignature α),
    ⊢ (t1 ≃ t2) ⇒ ((t3 ≃ t4) ⇒ (t1 * t3 ≃ t2 * t4))

class PeanoDeduction (α : Type) [BEq α] [LawfulBEq α] [ClassicalFOLDeduction PeanoSignature α] where
  zero_not_succ : ∀ (t : Term PeanoSignature α),
    ⊢ ¬(S' t ≃ 0)

  succ_inj : ∀ (t1 t2 : Term PeanoSignature α),
    ⊢ (S' t1 ≃ S' t2) ⇒ (t1 ≃ t2)

  add_zero : ∀ (t : Term PeanoSignature α),
    ⊢ (t + 0) ≃ t

  add_succ : ∀ (t1 t2 : Term PeanoSignature α),
    ⊢ (t1 + S' t2) ≃ S' (t1 + t2)

  mul_zero : ∀ (t : Term PeanoSignature α),
    ⊢ (t * 0) ≃ 0

  mul_succ : ∀ (t1 t2 : Term PeanoSignature α),
    ⊢ (t1 * S' t2) ≃ (t1 * t2) + t1

  induction : ∀ (p : Formula PeanoSignature α) (x : α),
    ⊢ p⟦x := 0⟧ ⇒ ((∀' x, p ⇒ p⟦x := S' (V x)⟧) ⇒ ∀' x, p)
