import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R} {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜)

theorem exists_isTwoBlockDiagonal_of_ne_zero (hM : M (inr unit) (inr unit) ≠ 0) :
    ∃ L L' : List (TransvectionStruct (Fin r ⊕ Unit) 𝕜),
      IsTwoBlockDiagonal ((L.map Matrix.TransvectionStruct.toMatrix).prod * M * (L'.map Matrix.TransvectionStruct.toMatrix).prod) := by
  let L : List (TransvectionStruct (Fin r ⊕ Unit) 𝕜) :=
    List.ofFn fun i : Fin r =>
      ⟨inl i, inr unit, by simp, -M (inl i) (inr unit) / M (inr unit) (inr unit)⟩
  let L' : List (TransvectionStruct (Fin r ⊕ Unit) 𝕜) :=
    List.ofFn fun i : Fin r =>
      ⟨inr unit, inl i, by simp, -M (inr unit) (inl i) / M (inr unit) (inr unit)⟩
  refine ⟨L, L', ?_⟩
  have A : L.map Matrix.TransvectionStruct.toMatrix = Matrix.Pivot.listTransvecCol M := by simp [L, Matrix.Pivot.listTransvecCol, Function.comp_def]
  have B : L'.map Matrix.TransvectionStruct.toMatrix = Matrix.Pivot.listTransvecRow M := by simp [L', Matrix.Pivot.listTransvecRow, Function.comp_def]
  rw [A, B]
  exact Matrix.Pivot.isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow M hM

