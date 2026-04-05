import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem trailingCoeff_mul {R : Type*} [Semiring R] [NoZeroDivisors R] (p q : R[X]) :
    (p * q).trailingCoeff = p.trailingCoeff * q.trailingCoeff := by
  rw [← Polynomial.reverse_leadingCoeff, Polynomial.reverse_mul_of_domain, leadingCoeff_mul, Polynomial.reverse_leadingCoeff,
    Polynomial.reverse_leadingCoeff]

