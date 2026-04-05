import Mathlib

open scoped Polynomial.Bivariate

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

theorem Bivariate.swap_monomial_monomial (n m : ℕ) (r : R) :
    swap (monomial n (monomial m r)) = (monomial m (monomial n r)) := by
  simp [← C_mul_X_pow_eq_monomial]; ac_rfl

