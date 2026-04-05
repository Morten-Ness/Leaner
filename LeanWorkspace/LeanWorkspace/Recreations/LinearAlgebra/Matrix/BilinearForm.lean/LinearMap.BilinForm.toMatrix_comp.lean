import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

variable [Fintype n] [Fintype o]

variable [DecidableEq n] (b : Basis n R₁ M₁)

variable {M₂' : Type*} [AddCommMonoid M₂'] [Module R₁ M₂']

variable (c : Basis o R₁ M₂')

variable [DecidableEq o]

theorem LinearMap.BilinForm.toMatrix_comp (B : BilinForm R₁ M₁) (l r : M₂' →ₗ[R₁] M₁) :
    BilinForm.toMatrix c (B.comp l r) =
      (LinearMap.toMatrix c b l)ᵀ * BilinForm.toMatrix b B * LinearMap.toMatrix c b r := LinearMap.toMatrix₂_compl₁₂ _ _ _ _ B _ _

