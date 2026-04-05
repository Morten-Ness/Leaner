import Mathlib

open scoped Polynomial.Bivariate

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

theorem Bivariate.swap_map_C (f : R[X]) : swap (f.map C) = C f := by
  induction f using Polynomial.induction_on' with
  | add => aesop
  | monomial n a => rw [map_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
    map_mul, map_pow, swap_Y, C_mul, C_pow, Bivariate.swap_C_C]

