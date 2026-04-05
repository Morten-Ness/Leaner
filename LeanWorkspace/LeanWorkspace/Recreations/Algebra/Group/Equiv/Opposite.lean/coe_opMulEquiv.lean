import Mathlib

variable {M α : Type*}

variable [CommMonoid M]

theorem coe_opMulEquiv : ⇑MulOpposite.opMulEquiv = op (α := M) := rfl

