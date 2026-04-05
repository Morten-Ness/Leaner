import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass N] [MulOneClass P]

theorem toMonoidHom_injective : Function.Injective (MulEquiv.toMonoidHom : M ≃* N → M →* N) := Function.Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

