import Mathlib

variable (α : Type*) [Mul α]

theorem coe_ofLexMulEquiv : ⇑(ofLexMulEquiv α) = ofLex := rfl

