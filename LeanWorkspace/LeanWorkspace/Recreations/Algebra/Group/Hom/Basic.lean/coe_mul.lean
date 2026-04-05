import Mathlib

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem coe_mul {M N} [One M] [MulOneClass N] (f g : OneHom M N) : ⇑(f * g) = ⇑f * ⇑g := rfl

