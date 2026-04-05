import Mathlib

variable {R : Type*} [CommSemiring R]

theorem homogenize_smul {S : Type*} [Semiring S] [Module S R] (c : S) (p : R[X]) (n : ℕ) :
    Polynomial.homogenize (c • p) n = c • Polynomial.homogenize p n := by
  simp [Polynomial.homogenize, Finset.smul_sum, MvPolynomial.smul_monomial]

