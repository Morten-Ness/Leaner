import Mathlib

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*}

theorem Matrix.mulVecLin_submatrix [Fintype n] [Fintype l] (f₁ : m → k) (e₂ : n ≃ l)
    (M : Matrix k l R) :
    (M.submatrix f₁ e₂).mulVecLin = funLeft R R f₁ ∘ₗ M.mulVecLin ∘ₗ funLeft _ _ e₂.symm := LinearMap.ext fun _ ↦ submatrix_mulVec_equiv _ _ _ _

