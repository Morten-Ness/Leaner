import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

variable [Fintype n] [Fintype o]

variable [DecidableEq n] (b : Basis n R₁ M₁)

theorem LinearMap.BilinForm.toMatrix_basisFun :
    BilinForm.toMatrix (Pi.basisFun R₁ n) = BilinForm.toMatrix' := by
  rw [BilinForm.toMatrix, BilinForm.toMatrix', LinearMap.toMatrix₂_basisFun]

