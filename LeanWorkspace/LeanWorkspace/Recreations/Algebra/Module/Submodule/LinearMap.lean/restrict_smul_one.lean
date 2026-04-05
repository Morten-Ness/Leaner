import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {ι : Type*}

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₁] [Module R₂ M₂] [Module R₃ M₃]

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃)

theorem restrict_smul_one
    {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] {p : Submodule R M}
    (μ : R) (h : ∀ x ∈ p, (μ • (1 : Module.End R M)) x ∈ p := fun _ ↦ p.smul_mem μ) :
    (μ • 1 : Module.End R M).restrict h = μ • (1 : Module.End R p) :=
  rfl

