import Mathlib

open scoped Polynomial.Bivariate

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

theorem Bivariate.swap_Y : swap (R := R) Y = (C X) := by simp

