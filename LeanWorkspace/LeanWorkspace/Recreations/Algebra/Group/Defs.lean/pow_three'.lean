import Mathlib

variable {G : Type*}

variable {M : Type*} [Monoid M] {a b c : M}

theorem pow_three' (a : M) : a ^ 3 = a * a * a := by rw [pow_succ, pow_two]

