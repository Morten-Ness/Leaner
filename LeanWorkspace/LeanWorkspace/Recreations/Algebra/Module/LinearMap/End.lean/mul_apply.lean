import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

theorem mul_apply (f g : Module.End R M) (x : M) : (f * g) x = f (g x) := rfl

