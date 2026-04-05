import Mathlib

variable {R : Type u} [EuclideanDomain R]

variable [DecidableEq R]

theorem gcd_zero_left (a : R) : EuclideanDomain.gcd 0 a = a := by
  rw [EuclideanDomain.gcd]
  exact if_pos rfl

