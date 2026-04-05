import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable {R S M N P : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [Module S M] [Module S N] [CompatibleSMul M N R S]

theorem restrictScalars_add (f g : M →ₗ[S] N) :
    (f + g).restrictScalars R = f.restrictScalars R + g.restrictScalars R := rfl

