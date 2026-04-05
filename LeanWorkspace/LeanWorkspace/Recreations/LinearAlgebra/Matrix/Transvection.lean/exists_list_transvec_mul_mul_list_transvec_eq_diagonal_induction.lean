import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R} {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜)

theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction
    (IH :
      ∀ M : Matrix (Fin r) (Fin r) 𝕜,
        ∃ (L₀ L₀' : List (TransvectionStruct (Fin r) 𝕜)) (D₀ : Fin r → 𝕜),
          (L₀.map Matrix.TransvectionStruct.toMatrix).prod * M * (L₀'.map Matrix.TransvectionStruct.toMatrix).prod = diagonal D₀)
    (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜) :
    ∃ (L L' : List (TransvectionStruct (Fin r ⊕ Unit) 𝕜)) (D : Fin r ⊕ Unit → 𝕜),
      (L.map Matrix.TransvectionStruct.toMatrix).prod * M * (L'.map Matrix.TransvectionStruct.toMatrix).prod = diagonal D := by
  rcases Matrix.Pivot.exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec M with ⟨L₁, L₁', hM⟩
  let M' := (L₁.map Matrix.TransvectionStruct.toMatrix).prod * M * (L₁'.map Matrix.TransvectionStruct.toMatrix).prod
  let M'' := toBlocks₁₁ M'
  rcases IH M'' with ⟨L₀, L₀', D₀, h₀⟩
  set c := M' (inr unit) (inr unit)
  refine
    ⟨L₀.map (Matrix.TransvectionStruct.sumInl Unit) ++ L₁, L₁' ++ L₀'.map (Matrix.TransvectionStruct.sumInl Unit),
      Sum.elim D₀ fun _ => M' (inr unit) (inr unit), ?_⟩
  suffices (L₀.map (Matrix.TransvectionStruct.toMatrix ∘ Matrix.TransvectionStruct.sumInl Unit)).prod * M' * (L₀'.map (Matrix.TransvectionStruct.toMatrix ∘ Matrix.TransvectionStruct.sumInl Unit)).prod =
      diagonal (Sum.elim D₀ fun _ => c) by
    simpa [M', c, Matrix.mul_assoc]
  have : M' = fromBlocks M'' 0 0 (diagonal fun _ => c) := by
    rw [← fromBlocks_toBlocks M', hM.1, hM.2]
    rfl
  rw [this]
  simp [h₀]

