import Mathlib

open scoped MatrixGroups

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

theorem induction_on {motive : PGL(n, R) → Prop} (g : PGL(n, R))
    (Matrix.ProjGenLinGroup.mk : ∀ g : GL n R, motive (Matrix.ProjGenLinGroup.mk g)) : motive g := Quotient.inductionOn g Matrix.ProjGenLinGroup.mk

