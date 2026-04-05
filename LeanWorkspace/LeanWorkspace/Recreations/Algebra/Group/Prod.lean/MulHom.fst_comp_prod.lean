import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [Mul M] [Mul N] [Mul P]

theorem fst_comp_prod (f : M →ₙ* N) (g : M →ₙ* P) : (MulHom.fst N P).comp (f.prod g) = f := ext fun _ => rfl

