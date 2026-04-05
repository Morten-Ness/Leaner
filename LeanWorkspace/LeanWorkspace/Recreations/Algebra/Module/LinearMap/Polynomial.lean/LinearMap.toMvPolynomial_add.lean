import Mathlib

open scoped Matrix

variable {R M₁ M₂ ι₁ ι₂ : Type*}

variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂]

variable [Module R M₁] [Module R M₂]

variable [Fintype ι₁] [Finite ι₂]

variable [DecidableEq ι₁]

variable (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂)

theorem toMvPolynomial_add (f g : M₁ →ₗ[R] M₂) :
    (f + g).toMvPolynomial b₁ b₂ = f.toMvPolynomial b₁ b₂ + g.toMvPolynomial b₁ b₂ := by
  unfold LinearMap.toMvPolynomial; simp only [map_add, Matrix.toMvPolynomial_add]

