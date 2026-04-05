import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_monomial (n : ℕ) (ha : a ≠ 0) : Polynomial.degree (monomial n a) = n := by
  rw [Polynomial.degree, support_monomial n ha, max_singleton, Nat.cast_withBot]

