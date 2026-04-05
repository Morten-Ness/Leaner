import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natTrailingDegree_le_natDegree (p : R[X]) : p.natTrailingDegree ≤ p.natDegree := by
  by_cases hp : p = 0
  · rw [hp, natDegree_zero, Polynomial.natTrailingDegree_zero]
  · exact le_natDegree_of_ne_zero (mt Polynomial.trailingCoeff_eq_zero.mp hp)

