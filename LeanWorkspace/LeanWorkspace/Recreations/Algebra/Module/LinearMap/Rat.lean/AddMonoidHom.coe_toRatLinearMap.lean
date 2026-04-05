import Mathlib

variable {M M₂ : Type*}

theorem AddMonoidHom.coe_toRatLinearMap [AddCommGroup M] [Module ℚ M] [AddCommGroup M₂]
    [Module ℚ M₂] (f : M →+ M₂) : ⇑f.toRatLinearMap = f := rfl

