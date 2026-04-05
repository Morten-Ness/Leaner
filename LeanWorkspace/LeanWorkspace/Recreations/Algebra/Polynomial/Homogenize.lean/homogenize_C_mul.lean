import Mathlib

variable {R : Type*} [CommSemiring R]

theorem homogenize_C_mul (c : R) (p : R[X]) (n : ℕ) :
    Polynomial.homogenize (C c * p) n = .C c * Polynomial.homogenize p n := by
  simp only [C_mul', Polynomial.homogenize_smul, MvPolynomial.C_mul']

