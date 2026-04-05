import Mathlib

variable {R : Type*} [CommSemiring R]

theorem homogenize_mul (p q : R[X]) {m n : ℕ} (hm : natDegree p ≤ m) (hn : natDegree q ≤ n) :
    Polynomial.homogenize (p * q) (m + n) = Polynomial.homogenize p m * Polynomial.homogenize q n := by
  apply Polynomial.homogenize_eq_of_isHomogeneous
  · apply_rules [MvPolynomial.IsHomogeneous.mul, Polynomial.isHomogeneous_homogenize]
  · simp [*]

