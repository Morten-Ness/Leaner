import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [CommRing α] [StarRing α]

theorem schur_complement_eq₂₂ [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m m α)
    (B : Matrix m n α) {D : Matrix n n α} (x : m → α) (y : n → α) [Invertible D]
    (hD : D.IsHermitian) :
    (star (x ⊕ᵥ y)) ᵥ* (Matrix.fromBlocks A B Bᴴ D) ⬝ᵥ (x ⊕ᵥ y) =
      (star ((D⁻¹ * Bᴴ) *ᵥ x + y)) ᵥ* D ⬝ᵥ ((D⁻¹ * Bᴴ) *ᵥ x + y) +
        (star x) ᵥ* (A - B * D⁻¹ * Bᴴ) ⬝ᵥ x := by
  simp [Function.star_sumElim, vecMul_fromBlocks, add_vecMul,
    dotProduct_mulVec, vecMul_sub, Matrix.mul_assoc, hD.eq,
    conjTranspose_nonsing_inv, star_mulVec]
  abel

