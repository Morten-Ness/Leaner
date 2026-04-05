import Mathlib

variable {n' : Type*} [DecidableEq n'] [Fintype n'] {R : Type*} [CommRing R]

theorem Commute.self_zpow (A : M) (n : ℤ) : Commute A (A ^ n) := Matrix.Commute.zpow_right (Commute.refl A) _

