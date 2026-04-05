import Mathlib

variable {G : Type*}

variable {M : Type*} [Monoid M] {a b c : M}

theorem pow_add (a : M) (m : ℕ) : ∀ n, a ^ (m + n) = a ^ m * a ^ n
  | 0 => by rw [Nat.add_zero, pow_zero, mul_one]
  | n + 1 => by rw [pow_succ, ← mul_assoc, ← pow_add, ← pow_succ, Nat.add_assoc]
