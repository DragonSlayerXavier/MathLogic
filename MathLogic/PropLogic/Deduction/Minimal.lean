import MathLogic.PropLogic.Syntax

open Formula

class MinimalDeduction (α : Type) where
  Pr : Formula α → Prop

  imp_intro : ∀ {p q : Formula α}, (Pr p → Pr q) → Pr (p ⇒ q)
  imp_el    : ∀ {p q : Formula α}, Pr (p ⇒ q) → Pr p → Pr q

  and_intro : ∀ {p q : Formula α}, Pr p → Pr q → Pr (p ∧ q)
  and_el_l  : ∀ {p q : Formula α}, Pr (p ∧ q) → Pr p
  and_el_r  : ∀ {p q : Formula α}, Pr (p ∧ q) → Pr q

  or_intro_l : ∀ {p q : Formula α}, Pr p → Pr (p ∨ q)
  or_intro_r : ∀ {p q : Formula α}, Pr q → Pr (p ∨ q)
  or_el      : ∀ {p q r : Formula α}, Pr (p ∨ q) → (Pr p → Pr r) → (Pr q → Pr r) → Pr r

-- Use 'prefix' instead of 'notation' for better parsing
prefix:50 "⊢ " => MinimalDeduction.Pr
