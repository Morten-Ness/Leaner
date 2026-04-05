import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [CommRing α] [StarRing α]

theorem fromBlocks₂₂ [Fintype n] [DecidableEq n] (A : Matrix m m α) (B : Matrix m n α)
    {D : Matrix n n α} (hD : D.IsHermitian) :
    (Matrix.fromBlocks A B Bᴴ D).IsHermitian ↔ (A - B * D⁻¹ * Bᴴ).IsHermitian := by
  rw [← Matrix.isHermitian_submatrix_equiv (Equiv.sumComm n m), Equiv.sumComm_apply,
    fromBlocks_submatrix_sum_swap_sum_swap]
  convert Matrix.IsHermitian.fromBlocks₁₁ _ _ hD <;> simp

