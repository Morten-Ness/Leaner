import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

theorem AddMonoidHom.coe_toNatLinearMap [AddCommMonoid M] [AddCommMonoid M₂] (f : M →+ M₂) :
    ⇑f.toNatLinearMap = f := rfl

