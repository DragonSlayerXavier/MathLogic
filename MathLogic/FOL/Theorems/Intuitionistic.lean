import MathLogic.FOL.Syntax
import MathLogic.FOL.Deduction.Intuitionistic
import MathLogic.FOL.Theorems.Minimal

variable {S : Signature} {α : Type} [BEq α] [LawfulBEq α] [IntuitionisticFOLDeduction S α]
