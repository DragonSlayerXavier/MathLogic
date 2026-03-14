import MathLogic.FOL.Deduction.Intuitionistic

class ClassicalFoldeduction (S : Signature) (α : Type) [BEq α] extends IntuitionisticFoldeduction S α where
  dne : ∀ {p : Formula S α}, Pr (¬¬p ⇒ p)
