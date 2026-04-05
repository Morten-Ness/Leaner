import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

theorem intCast_apply (z : ℤ) (m : N₁) : (z : Module.End R N₁) m = z • m := rfl

