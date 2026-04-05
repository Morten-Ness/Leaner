import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_fromBlocks_zero₁₂ (A : Matrix m m R) (C : Matrix n m R) (D : Matrix n n R) :
    (Matrix.fromBlocks A 0 C D).det = A.det * D.det := by
  rw [← Matrix.det_transpose, fromBlocks_transpose, transpose_zero, Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose,
    Matrix.det_transpose]

