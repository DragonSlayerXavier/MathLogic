structure Signature where
  Func : Type
  func_arity : Func → Nat
  Pred : Type
  pred_arity : Pred → Nat

inductive Term (S : Signature) (α : Type) where
  | var  : α → Term S α
  | func : (f : S.Func) → (List (Term S α)) → Term S α

inductive Formula (S : Signature) (α : Type) where
  | pred    : (p : S.Pred) → (List (Term S α)) → Formula S α
  | bot     : Formula S α
  | top     : Formula S α
  | conj    : Formula S α → Formula S α → Formula S α
  | disj    : Formula S α → Formula S α → Formula S α
  | impl    : Formula S α → Formula S α → Formula S α
  | bi_impl : Formula S α → Formula S α → Formula S α
  | neg     : Formula S α → Formula S α
  | forall_ : α → Formula S α → Formula S α
  | exists_ : α → Formula S α → Formula S α

variable {S : Signature} {α : Type} [BEq α]

def freeVarsTerm (t : Term S α) : List α :=
  match t with
  | .var y => [y]
  | .func _ ts => ts.flatMap freeVarsTerm

def substT (t : Term S α) (x : α) (s : Term S α) : Term S α :=
  match t with
  | .var y => if x == y then s else .var y
  | .func f ts => .func f (ts.map (substT · x s))

def isFreeIn (x : α) (A : Formula S α) : Bool :=
  match A with
  | .pred _ ts => (ts.flatMap freeVarsTerm).contains x
  | .bot | .top => false
  | .conj f1 f2 | .disj f1 f2 | .impl f1 f2 | .bi_impl f1 f2 =>
      isFreeIn x f1 || isFreeIn x f2
  | .neg f => isFreeIn x f
  | .forall_ y body | .exists_ y body =>
      if x == y then false else isFreeIn x body

def substF (A : Formula S α) (x : α) (s : Term S α) : Formula S α :=
  match A with
  | .pred p ts => .pred p (ts.map (substT · x s))
  | .bot => .bot
  | .top => .top
  | .conj f1 f2    => .conj (substF f1 x s) (substF f2 x s)
  | .disj f1 f2    => .disj (substF f1 x s) (substF f2 x s)
  | .impl f1 f2    => .impl (substF f1 x s) (substF f2 x s)
  | .bi_impl f1 f2 => .bi_impl (substF f1 x s) (substF f2 x s)
  | .neg f         => .neg (substF f x s)
  | .forall_ y body => if x == y then .forall_ y body else .forall_ y (substF body x s)
  | .exists_ y body => if x == y then .exists_ y body else .exists_ y (substF body x s)

def isFreeFor (s : Term S α) (x : α) (A : Formula S α) : Bool :=
  match A with
  | .pred _ _ | .bot | .top => true
  | .conj f1 f2 | .disj f1 f2 | .impl f1 f2 | .bi_impl f1 f2 =>
      isFreeFor s x f1 && isFreeFor s x f2
  | .neg f => isFreeFor s x f
  | .forall_ y body | .exists_ y body =>
      if x == y then true
      else if (freeVarsTerm s).contains y then false
      else isFreeFor s x body

class VariableSupply (α : Type) [BEq α] where
  fresh : List α → α
  fresh_is_fresh : ∀ (l : List α), l.contains (fresh l) = false

theorem contains_append_false {l1 l2 : List α} {v : α} :
  (l1 ++ l2).contains v = false → l1.contains v = false ∧ l2.contains v = false := by
  intro h
  rw[List.contains_append] at h
  exact Bool.or_eq_false_iff.mp h

prefix:max "!" => Term.var
notation "⊥" => Formula.bot
notation "⊤" => Formula.top
prefix:75 "¬" => Formula.neg
infixr:35 " ∧ " => Formula.conj
infixr:30 " ∨ " => Formula.disj
infixr:25 " ⇒ " => Formula.impl
infixr:20 " ⇔ " => Formula.bi_impl
notation:max "∀' " x ", " p:0 => Formula.forall_ x p
notation:max "∃' " x ", " p:0 => Formula.exists_ x p
notation A "⟦" x " := " t "⟧" => substF A x t
