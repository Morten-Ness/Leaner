import Mathlib

open scoped DirectSum

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable [DecidableEq ι]

variable {N : Type u₁} [AddCommMonoid N] [Module R N]

variable (φ : ∀ i, M i →ₗ[R] N)

theorem coe_toModule_eq_coe_toAddMonoid :
    (DirectSum.toModule R ι N φ : (⨁ i, M i) → N) = toAddMonoid fun i ↦ (φ i).toAddMonoidHom := rfl

