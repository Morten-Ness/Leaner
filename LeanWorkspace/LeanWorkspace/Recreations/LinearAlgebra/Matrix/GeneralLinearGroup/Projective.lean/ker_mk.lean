import Mathlib

open scoped MatrixGroups

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

theorem ker_mk : Matrix.ProjGenLinGroup.mk.ker = Subgroup.center (GL n R) := QuotientGroup.ker_mk' _

