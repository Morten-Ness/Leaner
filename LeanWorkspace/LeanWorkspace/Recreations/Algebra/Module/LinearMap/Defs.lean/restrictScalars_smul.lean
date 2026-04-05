import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable {R S M N P : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [Module S M] [Module S N] [CompatibleSMul M N R S]

variable {R₁ : Type*} [Semiring R₁] [Module R₁ N] [SMulCommClass S R₁ N] [SMulCommClass R R₁ N]

theorem restrictScalars_smul (c : R₁) (f : M →ₗ[S] N) :
    (c • f).restrictScalars R = c • f.restrictScalars R := rfl

