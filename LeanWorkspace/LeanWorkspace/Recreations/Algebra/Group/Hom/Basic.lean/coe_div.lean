import Mathlib

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem coe_div {M N} [One M] [DivisionMonoid N] (f g : OneHom M N) : ⇑(f / g) = ⇑f / ⇑g := rfl

