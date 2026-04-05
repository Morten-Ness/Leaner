import Mathlib

open scoped MatrixGroups

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

variable {M : Type*} [Monoid M]

variable [Fact (Even (Fintype.card n))] [LinearOrder R] [IsStrictOrderedRing R]

theorem signDet_mk (g : GL n R) : Matrix.ProjGenLinGroup.signDet (Matrix.ProjGenLinGroup.mk g) = Units.map signHom.toMonoidHom g.det := by
  rfl

