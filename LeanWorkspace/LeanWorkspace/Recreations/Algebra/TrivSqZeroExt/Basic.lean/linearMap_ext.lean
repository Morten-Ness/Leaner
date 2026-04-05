import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem linearMap_ext {N} [Semiring S] [AddCommMonoid R] [AddCommMonoid M] [AddCommMonoid N]
    [Module S R] [Module S M] [Module S N] ⦃f g : tsze R M →ₗ[S] N⦄
    (hl : ∀ r, f (TrivSqZeroExt.inl r) = g (TrivSqZeroExt.inl r)) (hr : ∀ m, f (TrivSqZeroExt.inr m) = g (TrivSqZeroExt.inr m)) : f = g := LinearMap.prod_ext (LinearMap.ext hl) (LinearMap.ext hr)

