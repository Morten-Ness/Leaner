import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable [Semiring R] [Semiring R₂]

variable [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂]

variable {τ₁₂ : R →+* R₂} {τ₂₁ : R₂ →+* R}

variable [RingHomInvPair τ₁₂ τ₂₁] [RingHomInvPair τ₂₁ τ₁₂]

variable (p : Submodule R M) (q : Submodule R₂ M₂)

theorem orderIsoMapComap_apply' (e : M ≃ₛₗ[τ₁₂] M₂) (p : Submodule R M) :
    Submodule.orderIsoMapComap e p = Submodule.comap (e.symm : M₂ →ₛₗ[τ₂₁] M) p := Submodule.map_equiv_eq_comap_symm p _

