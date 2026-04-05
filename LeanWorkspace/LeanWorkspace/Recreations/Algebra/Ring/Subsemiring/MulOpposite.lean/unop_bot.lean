import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem unop_bot : (⊥ : Subsemiring Rᵐᵒᵖ).unop = ⊥ := Subsemiring.opEquiv.symm.map_bot

