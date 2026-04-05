import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

theorem fst_comp_inl : (MonoidHom.fst M N).comp (MonoidHom.inl M N) = id M := rfl

