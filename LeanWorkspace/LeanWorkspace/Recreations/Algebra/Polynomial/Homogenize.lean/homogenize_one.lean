import Mathlib

variable {R : Type*} [CommSemiring R]

theorem homogenize_one (n : ℕ) : Polynomial.homogenize (1 : R[X]) n = .X 1 ^ n := by
  simpa using Polynomial.homogenize_C (1 : R) n

