import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [Mul M] [Mul N] [Mul P]

theorem prod_apply (f : M →ₙ* N) (g : M →ₙ* P) (x) : f.prod g x = (f x, g x) := rfl

