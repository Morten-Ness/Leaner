import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

variable [MulOneClass P]

theorem fst_comp_prod (f : M →* N) (g : M →* P) : (MonoidHom.fst N P).comp (f.prod g) = f := ext fun _ => rfl

