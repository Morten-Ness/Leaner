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

theorem toFun_eq_coe : e.toFun = e := by dsimp

