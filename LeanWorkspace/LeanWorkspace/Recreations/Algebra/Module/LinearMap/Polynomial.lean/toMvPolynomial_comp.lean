import Mathlib

open scoped Matrix

variable {R M₁ M₂ M₃ ι₁ ι₂ ι₃ : Type*}

variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]

variable [Module R M₁] [Module R M₂] [Module R M₃]

variable [Fintype ι₁] [Fintype ι₂] [Finite ι₃]

variable [DecidableEq ι₁] [DecidableEq ι₂]

variable (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂) (b₃ : Basis ι₃ R M₃)

theorem toMvPolynomial_comp (g : M₂ →ₗ[R] M₃) (f : M₁ →ₗ[R] M₂) (i : ι₃) :
    (g ∘ₗ f).toMvPolynomial b₁ b₃ i =
      bind₁ (f.toMvPolynomial b₁ b₂) (g.toMvPolynomial b₂ b₃ i) := by
  simp only [LinearMap.toMvPolynomial, toMatrix_comp b₁ b₂ b₃, Matrix.toMvPolynomial_mul]
  rfl

