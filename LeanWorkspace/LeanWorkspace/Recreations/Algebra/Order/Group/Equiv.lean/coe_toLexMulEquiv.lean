import Mathlib

variable (α : Type*) [Mul α]

theorem coe_toLexMulEquiv : ⇑(toLexMulEquiv α) = toLex := rfl

