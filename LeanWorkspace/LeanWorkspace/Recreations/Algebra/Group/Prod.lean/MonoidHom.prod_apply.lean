import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

variable [MulOneClass P]

theorem prod_apply (f : M →* N) (g : M →* P) (x) : f.prod g x = (f x, g x) := rfl

