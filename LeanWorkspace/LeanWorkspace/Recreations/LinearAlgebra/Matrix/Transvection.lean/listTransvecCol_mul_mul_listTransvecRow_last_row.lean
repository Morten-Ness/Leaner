import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R} {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜)

theorem listTransvecCol_mul_mul_listTransvecRow_last_row (hM : M (inr unit) (inr unit) ≠ 0)
    (i : Fin r) :
    ((Matrix.Pivot.listTransvecCol M).prod * M * (Matrix.Pivot.listTransvecRow M).prod) (inl i) (inr unit) = 0 := by
  have : Matrix.Pivot.listTransvecCol M = Matrix.Pivot.listTransvecCol (M * (Matrix.Pivot.listTransvecRow M).prod) := by
    simp [Matrix.Pivot.listTransvecCol, Matrix.Pivot.mul_listTransvecRow_last_col]
  rw [this, Matrix.mul_assoc]
  apply Matrix.Pivot.listTransvecCol_mul_last_col
  simpa [Matrix.Pivot.mul_listTransvecRow_last_col] using hM

