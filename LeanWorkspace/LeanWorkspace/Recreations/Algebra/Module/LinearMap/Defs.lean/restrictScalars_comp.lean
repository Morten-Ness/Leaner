import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable {R S M N P : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [Module S M] [Module S N] [CompatibleSMul M N R S]

variable {R₁ : Type*} [Semiring R₁] [Module R₁ N] [SMulCommClass S R₁ N] [SMulCommClass R R₁ N]

theorem restrictScalars_comp [AddCommMonoid P] [Module S P] [Module R P]
    [CompatibleSMul N P R S] [CompatibleSMul M P R S] (f : N →ₗ[S] P) (g : M →ₗ[S] N) :
    (f ∘ₗ g).restrictScalars R = f.restrictScalars R ∘ₗ g.restrictScalars R := rfl

