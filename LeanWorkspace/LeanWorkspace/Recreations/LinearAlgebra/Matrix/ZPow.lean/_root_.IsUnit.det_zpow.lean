import Mathlib

variable {n' : Type*} [DecidableEq n'] [Fintype n'] {R : Type*} [CommRing R]

theorem _root_.IsUnit.det_zpow {A : M} (h : IsUnit A.det) (n : ℤ) : IsUnit (A ^ n).det := by
  rcases n with n | n
  · simpa using h.pow n
  · simpa using h.pow n.succ

