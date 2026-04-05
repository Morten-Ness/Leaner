import Mathlib

variable {G : Type*}

variable {M : Type u} [MulOneClass M]

theorem mul_one : ∀ a : M, a * 1 = a := MulOneClass.mul_one

