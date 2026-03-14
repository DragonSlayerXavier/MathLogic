import MathLogic.PropLogic.Syntax
import MathLogic.PropLogic.Deduction.Minimal

open Formula

class ClassicalDeduction (α : Type) extends MinimalDeduction α where
  dne : ∀ {p : Formula α}, Pr (¬¬p ⇒ p)
