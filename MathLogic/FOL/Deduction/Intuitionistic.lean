import MathLogic.FOL.Deduction.Minimal

class IntuitionisticFOLDeduction (S : Signature) (α : Type) [BEq α] extends MinimalFOLDeduction S α where
  ex_falso : ∀ {p : Formula S α}, Pr (⊥ ⇒ p)
