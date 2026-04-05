import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [Mul M] [Mul N] [Mul P]

theorem coe_snd : ⇑(MulHom.snd M N) = Prod.snd := rfl

