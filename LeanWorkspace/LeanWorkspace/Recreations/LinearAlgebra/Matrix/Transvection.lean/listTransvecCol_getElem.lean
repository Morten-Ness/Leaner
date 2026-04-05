import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R} {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜)

theorem listTransvecCol_getElem {i : ℕ} (h : i < (Matrix.Pivot.listTransvecCol M).length) :
    (Matrix.Pivot.listTransvecCol M)[i] =
      letI i' : Fin r := ⟨i, Matrix.Pivot.length_listTransvecCol M ▸ h⟩
      Matrix.transvection (inl i') (inr unit) <| -M (inl i') (inr unit) / M (inr unit) (inr unit) := by
  simp [Matrix.Pivot.listTransvecCol]

