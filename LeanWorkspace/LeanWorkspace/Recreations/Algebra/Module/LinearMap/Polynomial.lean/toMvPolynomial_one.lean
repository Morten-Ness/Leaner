import Mathlib

open scoped Matrix

variable {m n o R S : Type*}

variable [Fintype n] [Fintype o] [CommSemiring R] [CommSemiring S]

theorem toMvPolynomial_one [DecidableEq n] : (1 : Matrix n n R).toMvPolynomial = X := by
  ext i : 1
  rw [Matrix.toMvPolynomial, Finset.sum_eq_single i]
  · simp only [one_apply_eq, ← C_mul_X_eq_monomial, C_1, one_mul]
  · rintro j - hj
    simp only [one_apply_ne hj.symm, map_zero]
  · grind

