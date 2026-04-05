import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

variable [Fintype n] [Fintype o]

variable [DecidableEq n] (b : Basis n R₁ M₁)

variable {M₂' : Type*} [AddCommMonoid M₂'] [Module R₁ M₂']

variable (c : Basis o R₁ M₂')

variable [DecidableEq o]

theorem LinearMap.BilinForm.toMatrix_compLeft (B : BilinForm R₁ M₁) (f : M₁ →ₗ[R₁] M₁) :
    BilinForm.toMatrix b (B.compLeft f) = (LinearMap.toMatrix b b f)ᵀ * BilinForm.toMatrix b B := LinearMap.toMatrix₂_comp _ _ _ B _

