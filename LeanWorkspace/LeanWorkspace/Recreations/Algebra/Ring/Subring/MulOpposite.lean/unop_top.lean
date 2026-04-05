import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem unop_top : (⊤ : Subring Rᵐᵒᵖ).unop = ⊤ := rfl

