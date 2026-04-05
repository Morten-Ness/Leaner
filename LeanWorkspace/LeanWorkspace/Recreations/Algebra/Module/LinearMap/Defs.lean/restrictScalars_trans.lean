import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable {R S M N P : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [Module S M] [Module S N] [CompatibleSMul M N R S]

variable {R₁ : Type*} [Semiring R₁] [Module R₁ N] [SMulCommClass S R₁ N] [SMulCommClass R R₁ N]

theorem restrictScalars_trans {T : Type*} [Semiring T] [Module T M] [Module T N]
    [CompatibleSMul M N S T] [CompatibleSMul M N R T] (f : M →ₗ[T] N) :
    (f.restrictScalars S).restrictScalars R = f.restrictScalars R := rfl

