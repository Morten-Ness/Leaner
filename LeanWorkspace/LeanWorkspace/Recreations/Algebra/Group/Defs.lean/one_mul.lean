import Mathlib

variable {G : Type*}

variable {M : Type u} [MulOneClass M]

theorem one_mul : ∀ a : M, 1 * a = a := MulOneClass.one_mul

