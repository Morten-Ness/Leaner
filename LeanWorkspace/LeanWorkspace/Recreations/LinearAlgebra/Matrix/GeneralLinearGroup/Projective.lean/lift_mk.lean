import Mathlib

open scoped MatrixGroups

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

variable {M : Type*} [Monoid M]

theorem lift_mk {f : GL n R →* M} (hf) (g : GL n R) : Matrix.ProjGenLinGroup.lift f hf (Matrix.ProjGenLinGroup.mk g) = f g := by
  rfl

