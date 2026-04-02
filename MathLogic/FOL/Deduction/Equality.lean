import MathLogic.FOL.Syntax
import MathLogic.FOL.Deduction.Minimal

class EqualityDeduction (S : Signature) (α : Type) [BEq α] [MinimalFOLDeduction S α] (eq_pred : S.Pred) where
  refl : ∀ (t : Term S α),
    ⊢ .pred eq_pred [t, t]

  symm : ∀ (t1 t2 : Term S α),
    ⊢ .pred eq_pred [t1, t2] ⇒ .pred eq_pred [t2, t1]

  trans : ∀ (t1 t2 t3 : Term S α),
    ⊢ .pred eq_pred [t1, t2] ⇒ (.pred eq_pred [t2, t3] ⇒ .pred eq_pred [t1, t3])
