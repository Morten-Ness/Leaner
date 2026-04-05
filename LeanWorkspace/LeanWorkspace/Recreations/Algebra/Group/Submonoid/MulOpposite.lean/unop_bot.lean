import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem unop_bot : (⊥ : Submonoid Mᵐᵒᵖ).unop = ⊥ := Submonoid.opEquiv.symm.map_bot

