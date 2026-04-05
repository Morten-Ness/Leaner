import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

variable [MulOneClass P]

theorem coe_prod (f : M →* N) (g : M →* P) : ⇑(f.prod g) = Pi.prod f g := rfl

