import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [CommRing α] [StarRing α]

theorem fromBlocks₁₁ [Fintype m] [DecidableEq m] {A : Matrix m m α} (B : Matrix m n α)
    (D : Matrix n n α) (hA : A.IsHermitian) :
    (Matrix.fromBlocks A B Bᴴ D).IsHermitian ↔ (D - Bᴴ * A⁻¹ * B).IsHermitian := by
  have hBAB : (Bᴴ * A⁻¹ * B).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul _ hA.inv
  rw [Matrix.isHermitian_fromBlocks_iff]
  exact ⟨fun h ↦ h.2.2.2.sub hBAB, fun h ↦ ⟨hA, rfl, conjTranspose_conjTranspose B,
    sub_add_cancel D _ ▸ h.add hBAB⟩⟩

