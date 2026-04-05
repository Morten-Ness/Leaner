import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

variable [MulOneClass P]

theorem prod_unique (f : M →* N × P) : ((MonoidHom.fst N P).comp f).prod ((MonoidHom.snd N P).comp f) = f := ext fun _ => by simp

