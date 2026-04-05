import Mathlib

variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]

variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}

variable {σ : R₁ →+* R₂} {σ' : R₂ →+* R₁}

variable [RingHomInvPair σ σ']

theorem symm (σ₁₂ : R₁ →+* R₂) (σ₂₁ : R₂ →+* R₁) [RingHomInvPair σ₁₂ σ₂₁] :
    RingHomInvPair σ₂₁ σ₁₂ := ⟨RingHomInvPair.comp_eq₂, RingHomInvPair.comp_eq⟩

