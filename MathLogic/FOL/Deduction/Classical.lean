import MathLogic.FOL.Deduction.Minimal

class ClassicalFOLDeduction (S : Signature) (α : Type) [BEq α] extends MinimalFOLDeduction S α where
  dne : ∀ {p : Formula S α}, Pr (¬¬p ⇒ p)

variable {S : Signature} {α : Type} [BEq α] [ClassicalFOLDeduction S α]

theorem ex_falso {p : Formula S α} : ⊢ ⊥ ⇒ p := by
  apply MinimalFOLDeduction.deduction
  intro hbot
  let h_nnp: ⊢ (¬¬p) := by
    apply MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_intro (¬p))
    apply MinimalFOLDeduction.deduction
    intro hnp
    exact hbot
  exact MinimalFOLDeduction.mp (ClassicalFOLDeduction.dne) h_nnp

-- Reductio ad absurdum
theorem proof_by_contradiction {p : Formula S α} : ⊢ (¬p ⇒ ⊥) ⇒ p := by
  apply MinimalFOLDeduction.deduction
  intro h
  have hnnp : ⊢ ¬¬p := by
    apply MinimalFOLDeduction.mp (MinimalFOLDeduction.neg_intro (¬p))
    apply MinimalFOLDeduction.deduction
    intro hnp
    exact MinimalFOLDeduction.mp h hnp
  exact MinimalFOLDeduction.mp (ClassicalFOLDeduction.dne) hnnp
