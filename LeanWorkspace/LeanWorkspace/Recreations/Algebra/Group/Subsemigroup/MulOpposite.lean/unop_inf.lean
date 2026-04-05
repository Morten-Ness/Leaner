import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_inf (S₁ S₂ : Subsemigroup Mᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop := rfl

