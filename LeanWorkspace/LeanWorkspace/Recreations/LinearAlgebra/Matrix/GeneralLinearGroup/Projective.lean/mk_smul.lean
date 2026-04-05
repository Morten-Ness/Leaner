import Mathlib

open scoped MatrixGroups

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

variable {M : Type*} [Monoid M]

theorem mk_smul {α : Type*} [MulAction (GL n R) α] (h) (g : GL n R) (a : α) :
    letI : MulAction (PGL(n, R)) α := Matrix.ProjGenLinGroup.mulActionOfGL h
    Matrix.ProjGenLinGroup.mk g • a = g • a := by
  rfl

