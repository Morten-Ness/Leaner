import Mathlib

open scoped MatrixGroups

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

theorem mk_scalar (u : Rˣ) : Matrix.ProjGenLinGroup.mk (.scalar n u) = 1 := by
  rw [← MonoidHom.mem_ker, Matrix.ProjGenLinGroup.ker_mk, GeneralLinearGroup.center_eq_range_scalar]
  simp

