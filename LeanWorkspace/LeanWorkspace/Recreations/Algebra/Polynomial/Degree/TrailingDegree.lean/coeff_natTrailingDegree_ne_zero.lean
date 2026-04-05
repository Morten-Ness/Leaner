import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_natTrailingDegree_ne_zero : coeff p p.natTrailingDegree ≠ 0 ↔ p ≠ 0 := coeff_natTrailingDegree_eq_zero.not

