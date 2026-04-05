import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

theorem natCast_apply (n : ℕ) (m : M) : (↑n : Module.End R M) m = n • m := rfl

