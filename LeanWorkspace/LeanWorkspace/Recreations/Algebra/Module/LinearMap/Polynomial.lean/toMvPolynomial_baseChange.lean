import Mathlib

open scoped Matrix

variable {R M₁ M₂ ι₁ ι₂ : Type*}

variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂]

variable [Module R M₁] [Module R M₂]

variable [Fintype ι₁] [Finite ι₂]

variable [DecidableEq ι₁]

variable (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂)

theorem toMvPolynomial_baseChange (f : M₁ →ₗ[R] M₂) (i : ι₂) (A : Type*) [CommRing A] [Algebra R A] :
    (f.baseChange A).toMvPolynomial (basis A b₁) (basis A b₂) i =
      MvPolynomial.map (algebraMap R A) (f.toMvPolynomial b₁ b₂ i) := by
  simp only [LinearMap.toMvPolynomial, toMatrix_baseChange, Matrix.toMvPolynomial_map]

