import Mathlib

variable {R : Type*} [CommSemiring R]

theorem homogenize_C (c : R) (n : ℕ) : Polynomial.homogenize (.C c) n = .C c * .X 1 ^ n := by
  simpa [MvPolynomial.C_mul_X_pow_eq_monomial] using Polynomial.homogenize_monomial (Nat.zero_le n) c

