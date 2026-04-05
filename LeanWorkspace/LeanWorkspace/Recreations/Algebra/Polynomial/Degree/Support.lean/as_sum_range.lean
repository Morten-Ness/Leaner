import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem as_sum_range (p : R[X]) : p = ∑ i ∈ range (p.natDegree + 1), monomial i (coeff p i) := Polynomial.as_sum_range' p _ (lt_add_one _)

