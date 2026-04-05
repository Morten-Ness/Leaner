import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable [Semiring R] [Semiring R₂]

variable [AddCommMonoid M] [AddCommMonoid M₂]

variable {module_M : Module R M} {module_M₂ : Module R₂ M₂}

variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}

variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}

variable (e : M ≃ₛₗ[σ₁₂] M₂)

theorem submoduleMap_symm_apply (p : Submodule R M)
    (x : (p.map (e : M →ₛₗ[σ₁₂] M₂) : Submodule R₂ M₂)) : ↑((e.submoduleMap p).symm x) = e.symm x := rfl

