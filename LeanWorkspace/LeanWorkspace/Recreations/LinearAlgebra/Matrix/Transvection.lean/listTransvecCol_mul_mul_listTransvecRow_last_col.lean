import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R} {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜)

theorem listTransvecCol_mul_mul_listTransvecRow_last_col (hM : M (inr unit) (inr unit) ≠ 0)
    (i : Fin r) :
    ((Matrix.Pivot.listTransvecCol M).prod * M * (Matrix.Pivot.listTransvecRow M).prod) (inr unit) (inl i) = 0 := by
  have : Matrix.Pivot.listTransvecRow M = Matrix.Pivot.listTransvecRow ((Matrix.Pivot.listTransvecCol M).prod * M) := by
    simp [Matrix.Pivot.listTransvecRow, Matrix.Pivot.listTransvecCol_mul_last_row]
  rw [this]
  apply Matrix.Pivot.mul_listTransvecRow_last_row
  simpa [Matrix.Pivot.listTransvecCol_mul_last_row] using hM

