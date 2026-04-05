import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_one_le : Polynomial.degree (1 : R[X]) ≤ (0 : WithBot ℕ) := by rw [← C_1]; exact Polynomial.degree_C_le

