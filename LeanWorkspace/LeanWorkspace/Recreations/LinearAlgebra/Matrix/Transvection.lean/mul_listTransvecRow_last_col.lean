import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R} {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜)

theorem mul_listTransvecRow_last_col (i : Fin r ⊕ Unit) :
    (M * (Matrix.Pivot.listTransvecRow M).prod) i (inr unit) = M i (inr unit) := by
  have A : (Matrix.Pivot.listTransvecRow M).length = r := by simp [Matrix.Pivot.listTransvecRow]
  rw [← List.take_length (l := Matrix.Pivot.listTransvecRow M), A]
  simpa using Matrix.Pivot.mul_listTransvecRow_last_col_take M i le_rfl

