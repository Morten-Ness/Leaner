import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Nontrivial R] {p q : R[X]} (n : ℕ)

theorem degree_mul_X : degree (p * Polynomial.X) = degree p + 1 := by simp [monic_X.degree_mul]

