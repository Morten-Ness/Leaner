import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem self_sub_C_mul_X_pow {R : Type*} [Ring R] (f : R[X]) :
    f - Polynomial.C f.leadingCoeff * Polynomial.X ^ f.natDegree = f.eraseLead := by
  rw [C_mul_X_pow_eq_monomial, Polynomial.self_sub_monomial_natDegree_leadingCoeff]

