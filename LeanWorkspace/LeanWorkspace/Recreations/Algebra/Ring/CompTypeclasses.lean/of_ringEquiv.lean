import Mathlib

variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]

variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}

variable {σ : R₁ →+* R₂} {σ' : R₂ →+* R₁}

variable [RingHomInvPair σ σ']

theorem of_ringEquiv (e : R₁ ≃+* R₂) : RingHomInvPair (↑e : R₁ →+* R₂) ↑e.symm := ⟨e.symm_toRingHom_comp_toRingHom, e.symm.symm_toRingHom_comp_toRingHom⟩

