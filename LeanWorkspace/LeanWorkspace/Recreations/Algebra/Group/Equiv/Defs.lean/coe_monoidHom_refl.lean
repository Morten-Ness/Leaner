import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass N] [MulOneClass P]

theorem coe_monoidHom_refl : (MulEquiv.refl M : M →* M) = MonoidHom.id M := rfl

