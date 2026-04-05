import Mathlib

variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]

variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}

variable {σ : R₁ →+* R₂} {σ' : R₂ →+* R₁}

theorem comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomSurjective σ₁₂] [RingHomSurjective σ₂₃] :
    RingHomSurjective σ₁₃ := { is_surjective := by
      have := σ₂₃.surjective.comp σ₁₂.surjective
      rwa [← RingHom.coe_comp, RingHomCompTriple.comp_eq] at this }

