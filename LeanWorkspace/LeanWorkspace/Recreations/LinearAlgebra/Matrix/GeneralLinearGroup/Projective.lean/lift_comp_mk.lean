import Mathlib

open scoped MatrixGroups

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

variable {M : Type*} [Monoid M]

theorem lift_comp_mk {f : GL n R →* M} (hf) : (Matrix.ProjGenLinGroup.lift f hf).comp Matrix.ProjGenLinGroup.mk = f := by
  rfl

