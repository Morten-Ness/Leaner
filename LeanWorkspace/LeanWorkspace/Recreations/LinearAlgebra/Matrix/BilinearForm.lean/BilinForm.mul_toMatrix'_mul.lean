import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

variable [Fintype n] [Fintype o]

variable [DecidableEq n] [DecidableEq o]

theorem BilinForm.mul_toMatrix'_mul (B : BilinForm R₁ (n → R₁)) (M : Matrix o n R₁)
    (N : Matrix n o R₁) : M * B.toMatrix' * N = (B.comp (Mᵀ).toLin' N.toLin').toMatrix' := B.mul_toMatrix₂'_mul _ _

