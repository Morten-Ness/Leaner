import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem unop_bot : (⊥ : Subring Rᵐᵒᵖ).unop = ⊥ := Subring.opEquiv.symm.map_bot

