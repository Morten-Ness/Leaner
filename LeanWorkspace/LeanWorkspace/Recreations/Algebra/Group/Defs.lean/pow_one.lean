import Mathlib

variable {G : Type*}

variable {M : Type*} [Monoid M] {a b c : M}

theorem pow_one (a : M) : a ^ 1 = a := by rw [pow_succ, pow_zero, one_mul]

