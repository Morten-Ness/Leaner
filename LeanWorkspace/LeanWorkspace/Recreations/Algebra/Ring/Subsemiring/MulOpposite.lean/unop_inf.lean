import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem unop_inf (S₁ S₂ : Subsemiring Rᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop := rfl

