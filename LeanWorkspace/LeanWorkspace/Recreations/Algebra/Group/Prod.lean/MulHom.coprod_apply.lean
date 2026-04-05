import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable [Mul M] [Mul N] [CommSemigroup P] (f : M →ₙ* P) (g : N →ₙ* P)

theorem coprod_apply (p : M × N) : f.coprod g p = f p.1 * g p.2 := rfl

