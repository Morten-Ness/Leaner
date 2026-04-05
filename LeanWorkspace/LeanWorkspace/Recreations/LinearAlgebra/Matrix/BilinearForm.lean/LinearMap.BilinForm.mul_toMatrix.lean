import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

variable [Fintype n] [Fintype o]

variable [DecidableEq n] (b : Basis n R₁ M₁)

variable {M₂' : Type*} [AddCommMonoid M₂'] [Module R₁ M₂']

variable (c : Basis o R₁ M₂')

variable [DecidableEq o]

theorem LinearMap.BilinForm.mul_toMatrix (B : BilinForm R₁ M₁) (M : Matrix n n R₁) :
    M * BilinForm.toMatrix b B = BilinForm.toMatrix b (B.compLeft (Matrix.toLin b b Mᵀ)) := LinearMap.mul_toMatrix₂ _ _ _ B _

