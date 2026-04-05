import Mathlib

variable {R : Type*} (n : Type*)

variable [NonUnitalNonAssocRing R] [Fintype n]

theorem matrix_monotone : Monotone (TwoSidedIdeal.matrix (R := R) n) :=
  fun _ _ IJ _ MI i j => IJ (MI i j)

