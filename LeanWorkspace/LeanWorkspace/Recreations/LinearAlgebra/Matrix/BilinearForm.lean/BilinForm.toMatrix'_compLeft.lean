import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

variable [Fintype n] [Fintype o]

variable [DecidableEq n] [DecidableEq o]

theorem BilinForm.toMatrix'_compLeft (B : BilinForm R₁ (n → R₁)) (f : (n → R₁) →ₗ[R₁] n → R₁) :
    (B.compLeft f).toMatrix' = f.toMatrix'ᵀ * B.toMatrix' := B.toMatrix₂'_comp _

