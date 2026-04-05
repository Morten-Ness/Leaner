import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R} {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜)

theorem isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow
    (hM : M (inr unit) (inr unit) ≠ 0) :
    IsTwoBlockDiagonal ((Matrix.Pivot.listTransvecCol M).prod * M * (Matrix.Pivot.listTransvecRow M).prod) := by
  constructor
  · ext i j
    have : j = unit := by simp only
    simp [toBlocks₁₂, this, Matrix.Pivot.listTransvecCol_mul_mul_listTransvecRow_last_row M hM]
  · ext i j
    have : i = unit := by simp only
    simp [toBlocks₂₁, this, Matrix.Pivot.listTransvecCol_mul_mul_listTransvecRow_last_col M hM]

