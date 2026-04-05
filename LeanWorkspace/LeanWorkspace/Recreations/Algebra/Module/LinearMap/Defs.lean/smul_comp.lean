import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable [Monoid S] [DistribMulAction S M₂] [SMulCommClass R₂ S M₂]

variable [Monoid S₃] [DistribMulAction S₃ M₃] [SMulCommClass R₃ S₃ M₃]

theorem smul_comp (a : S₃) (g : M₂ →ₛₗ[σ₂₃] M₃) (f : M →ₛₗ[σ₁₂] M₂) :
    (a • g).comp f = a • g.comp f := rfl

-- TODO: generalize this to semilinear maps

