import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N]
  [AddCommMonoid N'] [AddCommMonoid P] [AddCommMonoid P'] [Module R M]
  [Module R M'] [Module R N] [Module R N'] [Module R P] [Module R P']

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem iff_linearMap_rangeRestrict :
    Function.Exact f g ↔ Function.Exact (LinearMap.range f).subtype g.rangeRestrict := Function.MulExact.iff_rangeFactorization (zero_mem (LinearMap.range g))

alias ⟨linearMap_rangeRestrict, _⟩ := iff_linearMap_rangeRestrict

