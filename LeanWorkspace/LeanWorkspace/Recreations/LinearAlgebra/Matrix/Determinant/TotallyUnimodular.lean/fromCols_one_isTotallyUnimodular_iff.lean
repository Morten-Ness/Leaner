import Mathlib

variable {m m' n n' R : Type*} [CommRing R]

theorem fromCols_one_isTotallyUnimodular_iff [DecidableEq m] (A : Matrix m n R) :
    (fromCols A (1 : Matrix m m R)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  rw [← Matrix.transpose_isTotallyUnimodular_iff, transpose_fromCols, transpose_one,
    Matrix.fromRows_one_isTotallyUnimodular_iff, Matrix.transpose_isTotallyUnimodular_iff]

