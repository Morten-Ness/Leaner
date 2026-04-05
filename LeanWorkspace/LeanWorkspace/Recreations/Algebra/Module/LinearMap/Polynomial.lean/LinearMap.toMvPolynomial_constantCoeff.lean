import Mathlib

open scoped Matrix

variable {R M₁ M₂ ι₁ ι₂ : Type*}

variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂]

variable [Module R M₁] [Module R M₂]

variable [Fintype ι₁] [Finite ι₂]

variable [DecidableEq ι₁]

variable (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂)

theorem toMvPolynomial_constantCoeff (f : M₁ →ₗ[R] M₂) (i : ι₂) :
    constantCoeff (f.toMvPolynomial b₁ b₂ i) = 0 := Matrix.toMvPolynomial_constantCoeff _ _

