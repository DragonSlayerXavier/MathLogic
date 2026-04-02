import MathLogic.FOL.Syntax

inductive PeanoFunc
  | zero
  | succ
  | add
  | mul
  deriving DecidableEq

def peanoFuncArity : PeanoFunc → Nat
  | PeanoFunc.zero => 0
  | PeanoFunc.succ => 1
  | PeanoFunc.add => 2
  | PeanoFunc.mul => 2

inductive PeanoPred
  | eq
  deriving DecidableEq

def peanoPredArity : PeanoPred → Nat
  | PeanoPred.eq => 2

def PeanoSignature : Signature where
  Func := PeanoFunc
  func_arity := peanoFuncArity
  Pred := PeanoPred
  pred_arity := peanoPredArity

variable {α : Type}

instance : OfNat (Term PeanoSignature α) 0 where
  ofNat := .func PeanoFunc.zero []

def succ (t : Term PeanoSignature α) : Term PeanoSignature α :=
  .func PeanoFunc.succ [t]

prefix:max "S' " => succ

instance : Add (Term PeanoSignature α) where
  add t1 t2 := .func PeanoFunc.add [t1, t2]

instance : Mul (Term PeanoSignature α) where
  mul t1 t2 := .func PeanoFunc.mul [t1, t2]

def peanoEq (t1 t2 : Term PeanoSignature α) : Formula PeanoSignature α :=
  .pred PeanoPred.eq [t1, t2]

infix:50 " ≃ " => peanoEq
