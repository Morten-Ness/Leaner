import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

variable [Fintype n] [Fintype o]

variable [DecidableEq n] [DecidableEq o]

theorem Matrix.toBilin'_comp (M : Matrix n n R₁) (P Q : Matrix n o R₁) :
    M.toBilin'.comp P.toLin' Q.toLin' = (Pᵀ * M * Q).toBilin' := BilinForm.toMatrix'.injective
    (by simp only [LinearMap.BilinForm.toMatrix'_comp, LinearMap.BilinForm.toMatrix'_toBilin', toMatrix'_toLin'])

