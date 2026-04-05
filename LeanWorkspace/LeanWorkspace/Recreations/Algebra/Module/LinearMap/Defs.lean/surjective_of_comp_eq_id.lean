import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module S M₂] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ']

variable (f : M →ₛₗ[σ] M₂) (g : M₂ →ₛₗ[σ'] M) (h : g.comp f = .id)

theorem surjective_of_comp_eq_id : Function.Surjective g := .of_comp (g := f) <| by simp_rw [← LinearMap.coe_comp, h, LinearMap.id_coe, bijective_id.2]

