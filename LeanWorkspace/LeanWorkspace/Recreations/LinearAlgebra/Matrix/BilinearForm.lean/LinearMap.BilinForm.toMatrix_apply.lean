import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

variable [Fintype n] [Fintype o]

variable [DecidableEq n] (b : Basis n R₁ M₁)

theorem LinearMap.BilinForm.toMatrix_apply (B : BilinForm R₁ M₁) (i j : n) :
    BilinForm.toMatrix b B i j = B (b i) (b j) := LinearMap.toMatrix₂_apply _ _ B _ _

