import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

theorem fst_comp_inr : (MonoidHom.fst M N).comp (MonoidHom.inr M N) = 1 := rfl

