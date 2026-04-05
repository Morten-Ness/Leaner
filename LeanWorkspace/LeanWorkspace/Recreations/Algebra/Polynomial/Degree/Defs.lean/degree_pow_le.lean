import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem degree_pow_le (p : R[X]) : ∀ n : ℕ, Polynomial.degree (p ^ n) ≤ n • Polynomial.degree p
  | 0 => by rw [pow_zero, zero_nsmul]; exact Polynomial.degree_one_le
  | n + 1 => by grw [pow_succ, succ_nsmul, Polynomial.degree_mul_le, degree_pow_le]
