import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

variable [Fintype n] [Fintype o]

variable [DecidableEq n] (b : Basis n R₁ M₁)

theorem LinearMap.BilinForm.dotProduct_toMatrix_mulVec (B : BilinForm R₁ M₁) (x y : n → R₁) :
    x ⬝ᵥ (BilinForm.toMatrix b B) *ᵥ y = B (b.equivFun.symm x) (b.equivFun.symm y) := dotProduct_toMatrix₂_mulVec b b B x y

