import Mathlib

variable {G : Type*}

variable {M : Type*} [Monoid M] {a b c : M}

theorem pow_mul_comm' (a : M) (n : ℕ) : a ^ n * a = a * a ^ n := by rw [← pow_succ, pow_succ']

