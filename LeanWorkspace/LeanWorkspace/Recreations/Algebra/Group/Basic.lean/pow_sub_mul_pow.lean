import Mathlib

variable {α β G M : Type*}

variable [Monoid M] {a b : M} {m n : ℕ}

theorem pow_sub_mul_pow (a : M) (h : m ≤ n) : a ^ (n - m) * a ^ m = a ^ n := by
  rw [← pow_add, Nat.sub_add_cancel h]

