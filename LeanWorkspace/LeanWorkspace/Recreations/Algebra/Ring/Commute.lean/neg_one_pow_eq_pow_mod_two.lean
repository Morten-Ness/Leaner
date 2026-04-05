import Mathlib

variable {R : Type u}

variable [Ring R] {a : R} {n : ℕ}

theorem neg_one_pow_eq_pow_mod_two (n : ℕ) : (-1 : R) ^ n = (-1) ^ (n % 2) := by
  rw [← Nat.mod_add_div n 2, pow_add, pow_mul]; simp [sq]

