import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [Mul M] [Mul N] [Mul P]

theorem prod_unique (f : M →ₙ* N × P) : ((MulHom.fst N P).comp f).prod ((MulHom.snd N P).comp f) = f := ext fun x => by simp only [MulHom.prod_apply, MulHom.coe_fst, MulHom.coe_snd, comp_apply]

