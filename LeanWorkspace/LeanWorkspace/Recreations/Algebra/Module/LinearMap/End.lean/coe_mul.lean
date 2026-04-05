import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

theorem coe_mul (f g : Module.End R M) : ⇑(f * g) = f ∘ g := rfl

