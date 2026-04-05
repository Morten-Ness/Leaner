import Mathlib

open scoped Matrix

variable {m n o R S : Type*}

variable [Fintype n] [Fintype o] [CommSemiring R] [CommSemiring S]

theorem toMvPolynomial_add (M N : Matrix m n R) :
    (M + N).toMvPolynomial = M.toMvPolynomial + N.toMvPolynomial := by
  ext i : 1
  simp only [Matrix.toMvPolynomial, add_apply, map_add, Finset.sum_add_distrib, Pi.add_apply]

