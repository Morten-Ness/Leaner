import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

theorem inr_apply (y) : MonoidHom.inr M N y = (1, y) := rfl

