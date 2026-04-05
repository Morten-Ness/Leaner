import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [Mul M] [Mul N] [Mul P]

theorem snd_comp_prod (f : M →ₙ* N) (g : M →ₙ* P) : (MulHom.snd N P).comp (f.prod g) = g := ext fun _ => rfl

