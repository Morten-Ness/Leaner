import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

theorem LinearMap.BilinForm.toMatrixAux_apply (B : BilinForm R₁ M₁) (b : n → M₁) (i j : n) :
    BilinForm.toMatrixAux b B i j = B (b i) (b j) := LinearMap.toMatrix₂Aux_apply R₁ B _ _ _ _

