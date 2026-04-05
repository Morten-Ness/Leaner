import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]

variable [Semiring S] [Module S M] [SMulCommClass S R M]

theorem Module.End.intCast_def (z : ℤ) [AddCommGroup N₁] [Module R N₁] :
    (z : Module.End R N₁) = Module.toModuleEnd R N₁ z := rfl

