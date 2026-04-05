import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass N] [MulOneClass P]

theorem coe_toMonoidHom (e : M ≃* N) : ⇑e.toMonoidHom = e := rfl

