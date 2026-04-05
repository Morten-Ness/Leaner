import Mathlib

variable {G : Type*}

variable {M : Type*} [Monoid M] {a b c : M}

theorem pow_mul' (a : M) (m n : ℕ) : a ^ (m * n) = (a ^ n) ^ m := by rw [Nat.mul_comm, pow_mul]

