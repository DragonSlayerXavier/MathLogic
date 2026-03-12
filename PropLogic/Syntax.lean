inductive Formula (α : Type) where
  | var  : α → Formula α
  | bot  : Formula α
  | conj : Formula α → Formula α → Formula α
  | disj : Formula α → Formula α → Formula α
  | impl : Formula α → Formula α → Formula α

prefix:max "!" => Formula.var
notation "⊥" => Formula.bot
infixr:35 " ∧ " => Formula.conj
infixr:30 " ∨ " => Formula.disj
infixr:25 " ⇒ " => Formula.impl

def neg {α : Type} (p : Formula α) : Formula α :=
  p ⇒ ⊥

notation "¬" p => neg p
