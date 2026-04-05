import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem unop_inf (S₁ S₂ : Submonoid Mᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop := rfl

