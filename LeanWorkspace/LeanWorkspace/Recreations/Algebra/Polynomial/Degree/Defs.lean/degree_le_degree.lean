import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_le_degree (h : coeff q (Polynomial.natDegree p) ≠ 0) : Polynomial.degree p ≤ Polynomial.degree q := by
  by_cases hp : p = 0
  · rw [hp, Polynomial.degree_zero]
    exact bot_le
  · rw [Polynomial.degree_eq_natDegree hp]
    exact Polynomial.le_degree_of_ne_zero h

