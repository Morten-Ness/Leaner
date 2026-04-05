import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

theorem coe_fst : ⇑(MonoidHom.fst M N) = Prod.fst := rfl

