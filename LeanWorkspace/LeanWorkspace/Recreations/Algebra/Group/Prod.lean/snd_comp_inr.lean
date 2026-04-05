import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

theorem snd_comp_inr : (MonoidHom.snd M N).comp (MonoidHom.inr M N) = id N := rfl

