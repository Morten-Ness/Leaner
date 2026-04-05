import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

variable [Fintype n] [Fintype o]

variable [DecidableEq n] (b : Basis n R₁ M₁)

theorem LinearMap.BilinForm.toMatrixAux_eq (B : BilinForm R₁ M₁) :
    BilinForm.toMatrixAux (R₁ := R₁) b B = BilinForm.toMatrix b B :=
  LinearMap.toMatrix₂Aux_eq _ _ B

