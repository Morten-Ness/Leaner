import Mathlib

open scoped MatrixGroups

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

theorem mk_surjective : Function.Surjective (Matrix.ProjGenLinGroup.mk : GL n R → PGL(n, R)) := Quotient.mk_surjective

