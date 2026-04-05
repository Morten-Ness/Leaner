import Mathlib

variable (α : Type*) [Mul α]

theorem symm_ofLexMulEquiv : (ofLexMulEquiv α).symm = toLexMulEquiv α := rfl

