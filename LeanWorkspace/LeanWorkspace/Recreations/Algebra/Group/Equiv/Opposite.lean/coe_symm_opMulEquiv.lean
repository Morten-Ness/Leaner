import Mathlib

variable {M α : Type*}

variable [CommMonoid M]

theorem coe_symm_opMulEquiv : ⇑MulOpposite.opMulEquiv.symm = unop (α := M) := rfl

