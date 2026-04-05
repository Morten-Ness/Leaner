import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [Mul M] [Mul N] [Mul P]

theorem coe_prod (f : M →ₙ* N) (g : M →ₙ* P) : ⇑(f.prod g) = Pi.prod f g := rfl

