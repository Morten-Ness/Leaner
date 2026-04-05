import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

theorem coe_snd : ⇑(MonoidHom.snd M N) = Prod.snd := rfl

