import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_add_C_mul_X_pow (f : R[X]) :
    f.eraseLead + Polynomial.C f.leadingCoeff * Polynomial.X ^ f.natDegree = f := by
  rw [C_mul_X_pow_eq_monomial, Polynomial.eraseLead_add_monomial_natDegree_leadingCoeff]

