import MathLogic.FOL.Deduction.Minimal

class ClassicalFOLDeduction (S : Signature) (α : Type) [BEq α] extends MinimalFOLDeduction S α where
  dne : ∀ {p : Formula S α}, Pr (¬¬p ⇒ p)
