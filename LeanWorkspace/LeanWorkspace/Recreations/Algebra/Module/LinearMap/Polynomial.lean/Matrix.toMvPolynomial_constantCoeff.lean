import Mathlib

open scoped Matrix

variable {m n o R S : Type*}

variable [Fintype n] [Fintype o] [CommSemiring R] [CommSemiring S]

theorem toMvPolynomial_constantCoeff (M : Matrix m n R) (i : m) :
    constantCoeff (M.toMvPolynomial i) = 0 := by
  simp only [Matrix.toMvPolynomial, ← C_mul_X_eq_monomial, map_sum, map_mul, constantCoeff_X,
    mul_zero, Finset.sum_const_zero]

