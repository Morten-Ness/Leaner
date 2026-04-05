import Mathlib

variable {R : Type*} [CommSemiring R]

theorem aeval_homogenize_X_one (p : R[X]) {n : ℕ} (hn : natDegree p ≤ n) :
    MvPolynomial.aeval ![X, 1] (p.homogenize n) = p := by
  rw [Polynomial.aeval_homogenize_of_eq_one] <;> simp [*]

