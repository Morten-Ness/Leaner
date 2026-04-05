import Mathlib

open scoped Polynomial.Bivariate

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

theorem Bivariate.swap_monomial (n : ℕ) (f : R[X]) :
    swap (monomial n f) = f.map C * C (X ^ n) := by
  simp [← C_mul_X_pow_eq_monomial, aeval_X_left_eq_map]

