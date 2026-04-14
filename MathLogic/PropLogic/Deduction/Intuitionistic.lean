import MathLogic.PropLogic.Syntax
import MathLogic.PropLogic.Deduction.Minimal

open Formula

class IntuitionisticDeduction (α : Type) extends MinimalDeduction α where

  ex_falso : ∀ {p : Formula α}, Pr (⊥ ⇒ p)
