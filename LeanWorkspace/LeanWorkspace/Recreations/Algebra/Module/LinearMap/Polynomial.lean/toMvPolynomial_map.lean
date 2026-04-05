import Mathlib

open scoped Matrix

variable {m n o R S : Type*}

variable [Fintype n] [Fintype o] [CommSemiring R] [CommSemiring S]

theorem toMvPolynomial_map (f : R →+* S) (M : Matrix m n R) (i : m) :
    (M.map f).toMvPolynomial i = MvPolynomial.map f (M.toMvPolynomial i) := by
  simp only [Matrix.toMvPolynomial, map_apply, map_sum, map_monomial]

