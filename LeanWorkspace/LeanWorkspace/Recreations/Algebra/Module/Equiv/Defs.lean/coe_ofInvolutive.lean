import Mathlib

variable {R R₁ R₂ R₃ R₄ S M M₁ M₂ M₃ M₄ N₁ N₂ : Type*}

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M]

theorem coe_ofInvolutive {σ σ' : R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {_ : Module R M} (f : M →ₛₗ[σ] M) (hf : Function.Involutive f) : ⇑(LinearEquiv.ofInvolutive f hf) = f := rfl

