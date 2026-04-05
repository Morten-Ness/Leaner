import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_bot : (⊥ : Subsemigroup Mᵐᵒᵖ).unop = ⊥ := Subsemigroup.opEquiv.symm.map_bot

