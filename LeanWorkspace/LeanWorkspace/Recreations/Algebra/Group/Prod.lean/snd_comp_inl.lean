import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

theorem snd_comp_inl : (MonoidHom.snd M N).comp (MonoidHom.inl M N) = 1 := rfl

