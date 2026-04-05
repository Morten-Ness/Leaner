import Mathlib

variable {n' : Type*} [DecidableEq n'] [Fintype n'] {R : Type*} [CommRing R]

theorem Commute.zpow_self (A : M) (n : ℤ) : Commute (A ^ n) A := Matrix.Commute.zpow_left (Commute.refl A) _

