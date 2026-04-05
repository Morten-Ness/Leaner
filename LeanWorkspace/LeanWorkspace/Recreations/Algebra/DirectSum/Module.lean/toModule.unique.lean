import Mathlib

open scoped DirectSum

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable [DecidableEq ι]

variable {N : Type u₁} [AddCommMonoid N] [Module R N]

variable (φ : ∀ i, M i →ₗ[R] N)

variable (ψ : (⨁ i, M i) →ₗ[R] N)

theorem toModule.unique (f : ⨁ i, M i) : ψ f = DirectSum.toModule R ι N (fun i ↦ ψ.comp <| DirectSum.lof R ι M i) f := toAddMonoid.unique ψ.toAddMonoidHom f

