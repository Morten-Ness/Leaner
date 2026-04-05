import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem unop_top : (⊤ : Subsemiring Rᵐᵒᵖ).unop = ⊤ := rfl

