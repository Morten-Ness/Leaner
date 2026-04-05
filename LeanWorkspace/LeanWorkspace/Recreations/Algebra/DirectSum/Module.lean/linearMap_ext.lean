import Mathlib

open scoped DirectSum

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable [DecidableEq ι]

variable {N : Type u₁} [AddCommMonoid N] [Module R N]

variable (φ : ∀ i, M i →ₗ[R] N)

variable (ψ : (⨁ i, M i) →ₗ[R] N)

variable {ψ} {ψ' : (⨁ i, M i) →ₗ[R] N}

theorem linearMap_ext ⦃ψ ψ' : (⨁ i, M i) →ₗ[R] N⦄
    (H : ∀ i, ψ.comp (DirectSum.lof R ι M i) = ψ'.comp (DirectSum.lof R ι M i)) : ψ = ψ' := DFinsupp.lhom_ext' H

