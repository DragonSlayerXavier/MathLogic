import MathLogic.PropLogic.Syntax

open Formula

class MinimalDeduction (α : Type) where
  Pr : Formula α → Prop

  -- Rules of Inference
  mp        : ∀ {p q : Formula α}, Pr (p ⇒ q) → Pr p → Pr q
  deduction : ∀ {p q : Formula α}, (Pr p → Pr q) → Pr (p ⇒ q)

  -- I. Implication Axioms (K and S)
  aff_cons : ∀ (p q : Formula α), Pr (p ⇒ (q ⇒ p))
  dist_imp : ∀ (p q r : Formula α), Pr ((p ⇒ (q ⇒ r)) ⇒ ((p ⇒ q) ⇒ (p ⇒ r)))

  -- II. Conjunction Axioms
  conj_intro      : ∀ (p q : Formula α), Pr (p ⇒ (q ⇒ (p ∧ q)))
  conj_elim_left  : ∀ (p q : Formula α), Pr ((p ∧ q) ⇒ p)
  conj_elim_right : ∀ (p q : Formula α), Pr ((p ∧ q) ⇒ q)

  -- III. Disjunction Axioms
  disj_intro_left  : ∀ (p q : Formula α), Pr (p ⇒ (p ∨ q))
  disj_intro_right : ∀ (p q : Formula α), Pr (q ⇒ (p ∨ q))
  disj_elim        : ∀ (p q r : Formula α), Pr ((p ⇒ r) ⇒ ((q ⇒ r) ⇒ ((p ∨ q) ⇒ r)))

  -- IV. Negation and Truth Axioms
  trivial   : Pr ⊤
  neg_intro : ∀ (p : Formula α), Pr ((p ⇒ ⊥) ⇒ ¬p)
  neg_elim  : ∀ (p : Formula α), Pr (¬p ⇒ (p ⇒ ⊥))

  -- V. IFF (Bi-implication) Axioms
  iff_intro      : ∀ (p q : Formula α), Pr ((p ⇒ q) ⇒ ((q ⇒ p) ⇒ (p ⇔ q)))
  iff_elim_left  : ∀ (p q : Formula α), Pr ((p ⇔ q) ⇒ (p ⇒ q))
  iff_elim_right : ∀ (p q : Formula α), Pr ((p ⇔ q) ⇒ (q ⇒ p))

prefix:10 "⊢ " => MinimalDeduction.Pr
