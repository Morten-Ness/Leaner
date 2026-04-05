import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_mul (A : Matrix n n α) : Matrix.adjugate A * A = A.det • (1 : Matrix n n α) := calc
    Matrix.adjugate A * A = (Aᵀ * Matrix.adjugate Aᵀ)ᵀ := by
      rw [← Matrix.adjugate_transpose, ← transpose_mul, transpose_transpose]
    _ = _ := by rw [Matrix.mul_adjugate Aᵀ, det_transpose, transpose_smul, transpose_one]

