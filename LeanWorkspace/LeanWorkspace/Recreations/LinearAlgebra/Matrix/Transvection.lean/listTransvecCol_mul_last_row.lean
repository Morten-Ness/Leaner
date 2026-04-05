import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R} {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜)

theorem listTransvecCol_mul_last_row (i : Fin r ⊕ Unit) :
    ((Matrix.Pivot.listTransvecCol M).prod * M) (inr unit) i = M (inr unit) i := by
  simpa using Matrix.Pivot.listTransvecCol_mul_last_row_drop M i (zero_le _)

