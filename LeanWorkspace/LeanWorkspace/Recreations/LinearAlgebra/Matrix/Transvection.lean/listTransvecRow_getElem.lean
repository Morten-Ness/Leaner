import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R} {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜)

theorem listTransvecRow_getElem {i : ℕ} (h : i < (Matrix.Pivot.listTransvecRow M).length) :
    (Matrix.Pivot.listTransvecRow M)[i] =
      letI i' : Fin r := ⟨i, Matrix.Pivot.length_listTransvecRow M ▸ h⟩
      Matrix.transvection (inr unit) (inl i') <| -M (inr unit) (inl i') / M (inr unit) (inr unit) := by
  simp [Matrix.Pivot.listTransvecRow]

