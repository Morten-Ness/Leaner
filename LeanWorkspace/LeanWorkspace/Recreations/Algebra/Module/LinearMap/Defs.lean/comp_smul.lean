import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable [Monoid S] [DistribMulAction S M₂] [SMulCommClass R₂ S M₂]

variable [Monoid S₃] [DistribMulAction S₃ M₃] [SMulCommClass R₃ S₃ M₃]

theorem comp_smul [Module R M₂] [Module R M₃] [SMulCommClass R S M₂] [DistribMulAction S M₃]
    [SMulCommClass R S M₃] [CompatibleSMul M₃ M₂ S R] (g : M₃ →ₗ[R] M₂) (a : S) (f : M →ₗ[R] M₃) :
    g.comp (a • f) = a • g.comp f := LinearMap.ext fun _ ↦ LinearMap.map_smul_of_tower g _ _

