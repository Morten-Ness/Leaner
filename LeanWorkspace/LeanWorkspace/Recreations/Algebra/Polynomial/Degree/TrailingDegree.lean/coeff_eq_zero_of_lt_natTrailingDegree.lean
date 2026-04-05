import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_eq_zero_of_lt_natTrailingDegree {p : R[X]} {n : ℕ} (h : n < p.natTrailingDegree) :
    p.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_lt_trailingDegree
  by_cases hp : p = 0
  · rw [hp, Polynomial.trailingDegree_zero]
    exact WithTop.coe_lt_top n
  · rw [Polynomial.trailingDegree_eq_natTrailingDegree hp]
    exact WithTop.coe_lt_coe.2 h

