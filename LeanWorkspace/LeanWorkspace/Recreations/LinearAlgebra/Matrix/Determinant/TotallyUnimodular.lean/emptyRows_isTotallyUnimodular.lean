import Mathlib

variable {m m' n n' R : Type*} [CommRing R]

theorem emptyRows_isTotallyUnimodular [IsEmpty m] (A : Matrix m n R) :
    A.IsTotallyUnimodular := by
  intro k f _ _ _
  cases k with
  | zero => use 1; rw [submatrix_empty, det_fin_zero, SignType.coe_one]
  | succ => exact (IsEmpty.false (f 0)).elim

