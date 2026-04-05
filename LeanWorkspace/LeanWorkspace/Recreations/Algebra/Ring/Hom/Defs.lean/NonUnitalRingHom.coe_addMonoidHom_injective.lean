import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

theorem coe_addMonoidHom_injective : Function.Injective fun f : α →ₙ+* β => (f : α →+ β) := Function.Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

