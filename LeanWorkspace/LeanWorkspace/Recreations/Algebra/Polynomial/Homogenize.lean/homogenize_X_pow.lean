import Mathlib

variable {R : Type*} [CommSemiring R]

theorem homogenize_X_pow {m n : ℕ} (h : m ≤ n) :
    Polynomial.homogenize (X ^ m : R[X]) n = .X 0 ^ m * .X 1 ^ (n - m) := by
  rw [X_pow_eq_monomial, Polynomial.homogenize_monomial h, Finsupp.update_eq_add_single (by simp),
    MvPolynomial.monomial_single_add, ← MvPolynomial.X_pow_eq_monomial]

