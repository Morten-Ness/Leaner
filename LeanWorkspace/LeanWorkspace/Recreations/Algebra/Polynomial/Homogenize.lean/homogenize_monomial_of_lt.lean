import Mathlib

variable {R : Type*} [CommSemiring R]

theorem homogenize_monomial_of_lt {m n : ℕ} (h : n < m) (r : R) :
    Polynomial.homogenize (monomial m r) n = 0 := by
  rw [Polynomial.homogenize]
  apply Finset.sum_eq_zero
  aesop (add simp coeff_monomial)

