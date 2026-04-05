import Mathlib

variable {m m' n n' R : Type*} [CommRing R]

theorem fromCols_replicateCol0_isTotallyUnimodular_iff (A : Matrix m n R) :
    (fromCols A (replicateCol n' 0)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  rw [← Matrix.transpose_isTotallyUnimodular_iff, transpose_fromCols, transpose_replicateCol,
    Matrix.fromRows_replicateRow0_isTotallyUnimodular_iff, Matrix.transpose_isTotallyUnimodular_iff]

