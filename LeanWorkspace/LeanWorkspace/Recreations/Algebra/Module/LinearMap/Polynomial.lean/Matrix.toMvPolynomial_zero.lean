import Mathlib

open scoped Matrix

variable {m n o R S : Type*}

variable [Fintype n] [Fintype o] [CommSemiring R] [CommSemiring S]

theorem toMvPolynomial_zero : (0 : Matrix m n R).toMvPolynomial = 0 := by
  ext; simp only [Matrix.toMvPolynomial, zero_apply, map_zero, Finset.sum_const_zero, Pi.zero_apply]

