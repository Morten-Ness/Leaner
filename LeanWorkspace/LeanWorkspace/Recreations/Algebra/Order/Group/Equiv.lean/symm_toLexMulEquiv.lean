import Mathlib

variable (α : Type*) [Mul α]

theorem symm_toLexMulEquiv : (toLexMulEquiv α).symm = ofLexMulEquiv α := rfl

