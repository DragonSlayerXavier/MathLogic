import MathLogic.PropLogic.Syntax

open Formula

class MinimalDeduction (α : Type) where
  Pr : Formula α → Prop


  mp        : ∀ {p q : Formula α}, Pr (p ⇒ q) → Pr p → Pr q
  deduction : ∀ {p q : Formula α}, (Pr p → Pr q) → Pr (p ⇒ q)


  aff_cons : ∀ (p q : Formula α), Pr (p ⇒ (q ⇒ p))
  dist_imp : ∀ (p q r : Formula α), Pr ((p ⇒ (q ⇒ r)) ⇒ ((p ⇒ q) ⇒ (p ⇒ r)))


  conj_intro      : ∀ (p q : Formula α), Pr (p ⇒ (q ⇒ (p ∧ q)))
  conj_elim_left  : ∀ (p q : Formula α), Pr ((p ∧ q) ⇒ p)
  conj_elim_right : ∀ (p q : Formula α), Pr ((p ∧ q) ⇒ q)


  disj_intro_left  : ∀ (p q : Formula α), Pr (p ⇒ (p ∨ q))
  disj_intro_right : ∀ (p q : Formula α), Pr (q ⇒ (p ∨ q))
  disj_elim        : ∀ (p q r : Formula α), Pr ((p ⇒ r) ⇒ ((q ⇒ r) ⇒ ((p ∨ q) ⇒ r)))


  trivial   : Pr ⊤
  neg_intro : ∀ (p : Formula α), Pr ((p ⇒ ⊥) ⇒ ¬p)
  neg_elim  : ∀ (p : Formula α), Pr (¬p ⇒ (p ⇒ ⊥))


  iff_intro      : ∀ (p q : Formula α), Pr ((p ⇒ q) ⇒ ((q ⇒ p) ⇒ (p ⇔ q)))
  iff_elim_left  : ∀ (p q : Formula α), Pr ((p ⇔ q) ⇒ (p ⇒ q))
  iff_elim_right : ∀ (p q : Formula α), Pr ((p ⇔ q) ⇒ (q ⇒ p))

prefix:10 "⊢ " => MinimalDeduction.Pr
