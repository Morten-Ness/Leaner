import Mathlib

variable {R : Type*} [CommSemiring R]

theorem homogenize_zero (n : ℕ) : Polynomial.homogenize (0 : R[X]) n = 0 := by
  simp [Polynomial.homogenize]

