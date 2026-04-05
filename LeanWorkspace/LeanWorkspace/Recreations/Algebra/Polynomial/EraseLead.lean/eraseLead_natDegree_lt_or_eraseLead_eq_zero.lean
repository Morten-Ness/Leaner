import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_natDegree_lt_or_eraseLead_eq_zero (f : R[X]) :
    (Polynomial.eraseLead f).natDegree < f.natDegree ∨ f.eraseLead = 0 := by
  by_cases! h : #f.support ≤ 1
  · right
    rw [← C_mul_X_pow_eq_self h]
    simp
  · left
    apply Polynomial.eraseLead_natDegree_lt h

