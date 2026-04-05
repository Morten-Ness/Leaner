import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem op_sup (S₁ S₂ : Subring R) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op := Subring.opEquiv.map_sup _ _

