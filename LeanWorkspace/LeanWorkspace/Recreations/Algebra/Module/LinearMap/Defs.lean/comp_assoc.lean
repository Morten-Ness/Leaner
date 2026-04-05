import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [Semiring S]

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable {module_M₁ : Module R₁ M₁} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}

variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₂] M₂)

theorem comp_assoc
    {R₄ M₄ : Type*} [Semiring R₄] [AddCommMonoid M₄] [Module R₄ M₄]
    {σ₃₄ : R₃ →+* R₄} {σ₂₄ : R₂ →+* R₄} {σ₁₄ : R₁ →+* R₄}
    [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]
    (f : M₁ →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃) (h : M₃ →ₛₗ[σ₃₄] M₄) :
    ((h.comp g : M₂ →ₛₗ[σ₂₄] M₄).comp f : M₁ →ₛₗ[σ₁₄] M₄) = h.comp (g.comp f : M₁ →ₛₗ[σ₁₃] M₃) := rfl

