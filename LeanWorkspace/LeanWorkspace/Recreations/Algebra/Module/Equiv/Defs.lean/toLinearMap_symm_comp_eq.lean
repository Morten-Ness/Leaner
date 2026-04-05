import Mathlib

variable {R R₁ R₂ R₃ R₄ S M M₁ M₂ M₃ M₄ N₁ N₂ : Type*}

variable [Semiring R] [Semiring S]

variable [Semiring R₁] [Semiring R₂] [Semiring R₃] [Semiring R₄]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [AddCommMonoid M₄]

variable [AddCommMonoid N₁] [AddCommMonoid N₂]

variable {module_M : Module R M} {module_S_M₂ : Module S M₂} {σ : R →+* S} {σ' : S →+* R}

variable {re₁ : RingHomInvPair σ σ'} {re₂ : RingHomInvPair σ' σ}

variable (e e' : M ≃ₛₗ[σ] M₂)

variable {module_M₁ : Module R₁ M₁} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}

variable {module_M₄ : Module R₄ M₄} {module_N₁ : Module R₁ N₁} {module_N₂ : Module R₁ N₂}

variable {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}

variable {σ₁₃ : R₁ →+* R₃} {σ₃₁ : R₃ →+* R₁} [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]

variable {σ₁₄ : R₁ →+* R₄} {σ₄₁ : R₄ →+* R₁} [RingHomInvPair σ₁₄ σ₄₁] [RingHomInvPair σ₄₁ σ₁₄]

variable {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂}

variable {σ₂₄ : R₂ →+* R₄} {σ₄₂ : R₄ →+* R₂} [RingHomInvPair σ₂₄ σ₄₂] [RingHomInvPair σ₄₂ σ₂₄]

variable {σ₃₄ : R₃ →+* R₄} {σ₄₃ : R₄ →+* R₃} [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]

variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}

variable {re₂₃ : RingHomInvPair σ₂₃ σ₃₂} {re₃₂ : RingHomInvPair σ₃₂ σ₂₃}

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]

variable [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] [RingHomCompTriple σ₄₂ σ₂₁ σ₄₁]

variable [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₄₃ σ₃₁ σ₄₁]

variable [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₄₃ σ₃₂ σ₄₂]

variable (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃)

variable [RingHomCompTriple σ₂₁ σ₁₃ σ₂₃] [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂]

theorem toLinearMap_symm_comp_eq (f : M₃ →ₛₗ[σ₃₁] M₁) (g : M₃ →ₛₗ[σ₃₂] M₂) :
    e₁₂.symm.toLinearMap.comp g = f ↔ g = e₁₂.toLinearMap.comp f := by
  constructor <;> intro H <;> LinearEquiv.ext
  · simp [← H]
  · simp [H]

