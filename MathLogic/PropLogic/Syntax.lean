inductive Formula (α : Type) where
  | var  : α → Formula α
  | bot  : Formula α
  | top  : Formula α
  | conj : Formula α → Formula α → Formula α
  | disj : Formula α → Formula α → Formula α
  | impl : Formula α → Formula α → Formula α
  | bi_impl : Formula α → Formula α → Formula α
  | neg : Formula α → Formula α

prefix:max "!" => Formula.var
notation "⊥" => Formula.bot
notation "⊤" => Formula.top
prefix:75 "¬" => Formula.neg
infixr:35 " ∧ " => Formula.conj
infixr:30 " ∨ " => Formula.disj
infixr:25 " ⇒ " => Formula.impl
infixr:20 " ⇔ " => Formula.bi_impl
