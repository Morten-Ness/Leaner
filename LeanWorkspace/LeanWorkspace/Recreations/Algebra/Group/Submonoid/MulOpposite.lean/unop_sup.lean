import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem unop_sup (S₁ S₂ : Submonoid Mᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop := Submonoid.opEquiv.symm.map_sup _ _

