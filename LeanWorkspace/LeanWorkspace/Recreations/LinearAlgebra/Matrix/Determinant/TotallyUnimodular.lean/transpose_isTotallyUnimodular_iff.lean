import Mathlib

variable {m m' n n' R : Type*} [CommRing R]

theorem transpose_isTotallyUnimodular_iff (A : Matrix m n R) :
    Aᵀ.IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  constructor <;> apply Matrix.IsTotallyUnimodular.transpose

