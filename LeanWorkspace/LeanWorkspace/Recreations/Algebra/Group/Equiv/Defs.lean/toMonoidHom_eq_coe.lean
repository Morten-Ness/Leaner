import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass N] [MulOneClass P]

theorem toMonoidHom_eq_coe (f : M ≃* N) : f.toMonoidHom = (f : M →* N) := rfl

