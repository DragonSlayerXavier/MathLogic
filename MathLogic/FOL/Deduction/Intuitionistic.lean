import MathLogic.FOL.Deduction.Minimal

class IntuitionisticFoldeduction (S : Signature) (α : Type) [BEq α] extends MinimalFoldeduction S α where
  ex_falso : ∀ {p : Formula S α}, Pr (⊥ ⇒ p)
