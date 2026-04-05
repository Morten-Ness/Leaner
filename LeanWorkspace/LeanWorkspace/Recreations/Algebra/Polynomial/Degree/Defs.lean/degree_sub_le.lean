import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R] {p q : R[X]}

theorem degree_sub_le (p q : R[X]) : Polynomial.degree (p - q) ≤ max (Polynomial.degree p) (Polynomial.degree q) := by
  simpa only [Polynomial.degree_neg q] using Polynomial.degree_add_le p (-q)

