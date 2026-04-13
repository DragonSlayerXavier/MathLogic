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

  theorem substT_id (t : Term PeanoSignature α) (x : α) (s : Term PeanoSignature α)
  [BEq α] [LawfulBEq α] [MinimalFOLDeduction PeanoSignature α]
  (h : (freeVarsTerm t).contains x = false) :
  substT t x s = t := by
  let p : Formula PeanoSignature α := t ≃ t
  have h_nf : isFreeIn x p = false := by
    unfold p isFreeIn peanoEq
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.contains_eq_mem,
      List.mem_append, or_self, decide_eq_false_iff_not]
    simp only [List.contains_eq_mem, decide_eq_false_iff_not] at h
    exact h
  have h_sub := MinimalFOLDeduction.subst_id p x s h_nf
  unfold p substF peanoEq at h_sub
  injection h_sub with _ h_list
  injection h_list with h_head _

  theorem substT_succ (t : Term PeanoSignature α) (x : α) (s : Term PeanoSignature α) [BEq α] :
  substT (S' t) x s = S' (substT t x s) := by
  unfold succ
  rw [substT]
  simp only [List.map_cons, List.map_nil]

theorem substT_add (t1 t2 : Term PeanoSignature α) (x : α) (s : Term PeanoSignature α) [BEq α] :
  substT (t1 + t2) x s = (substT t1 x s + substT t2 x s) := by
  show substT (Term.func PeanoFunc.add [t1, t2]) x s =
       Term.func PeanoFunc.add [substT t1 x s, substT t2 x s]
  rw [substT]
  simp only [List.map_cons, List.map_nil]

theorem substT_mul (t1 t2 : Term PeanoSignature α) (x : α) (s : Term PeanoSignature α) [BEq α] :
  substT (t1 * t2) x s = (substT t1 x s * substT t2 x s) := by
  show substT (Term.func PeanoFunc.mul [t1, t2]) x s =
       Term.func PeanoFunc.mul [substT t1 x s, substT t2 x s]
  rw [substT]
  simp only [List.map_cons, List.map_nil]

theorem substT_var_same (x : α) (s : Term PeanoSignature α) [BEq α] [LawfulBEq α] :
  substT (V x) x s = s := by
  unfold V substT
  simp only [beq_self_eq_true, ↓reduceIte]

theorem substT_var_diff (x y : α) (s : Term PeanoSignature α) [BEq α] (h : (x == y) = false) :
  substT (V y) x s = V y := by
  unfold V substT
  simp only [h, Bool.false_eq_true, ↓reduceIte]
