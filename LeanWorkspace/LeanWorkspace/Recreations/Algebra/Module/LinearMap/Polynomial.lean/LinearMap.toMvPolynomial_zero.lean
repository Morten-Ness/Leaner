import Mathlib

open scoped Matrix

variable {R M₁ M₂ ι₁ ι₂ : Type*}

variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂]

variable [Module R M₁] [Module R M₂]

variable [Fintype ι₁] [Finite ι₂]

variable [DecidableEq ι₁]

variable (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂)

theorem toMvPolynomial_zero : (0 : M₁ →ₗ[R] M₂).toMvPolynomial b₁ b₂ = 0 := by
  unfold LinearMap.toMvPolynomial; simp only [map_zero, Matrix.toMvPolynomial_zero]

