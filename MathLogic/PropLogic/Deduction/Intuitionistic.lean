import MathLogic.PropLogic.Syntax
import MathLogic.PropLogic.Deduction.Minimal

open Formula

class IntuitionisticDeduction (α : Type) extends MinimalDeduction α where
  -- Use the field name 'Pr' here instead of the turnstile
  ex_falso : ∀ {p : Formula α}, Pr (⊥ ⇒ p)
