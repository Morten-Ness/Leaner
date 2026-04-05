import Mathlib

variable {α β G M : Type*}

variable [Monoid M] {a b : M} {m n : ℕ}

theorem pow_mul_pow_sub (a : M) (h : m ≤ n) : a ^ m * a ^ (n - m) = a ^ n := by
  rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel h]

