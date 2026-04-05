import Mathlib

open scoped Matrix

variable {R M₁ M₂ ι₁ ι₂ : Type*}

variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂]

variable [Module R M₁] [Module R M₂]

variable [Fintype ι₁] [Finite ι₂]

variable [DecidableEq ι₁]

variable (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂)

theorem toMvPolynomial_id : (id : M₁ →ₗ[R] M₁).toMvPolynomial b₁ b₁ = X := by
  unfold LinearMap.toMvPolynomial; simp only [toMatrix_id, Matrix.toMvPolynomial_one]

