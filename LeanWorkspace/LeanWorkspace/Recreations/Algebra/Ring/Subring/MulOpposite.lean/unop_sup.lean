import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem unop_sup (S₁ S₂ : Subring Rᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop := Subring.opEquiv.symm.map_sup _ _

