import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Nontrivial R] {p q : R[X]} (n : ℕ)

theorem degree_mul_X_pow : degree (p * Polynomial.X ^ n) = degree p + n := by simp [(monic_X_pow n).degree_mul]

