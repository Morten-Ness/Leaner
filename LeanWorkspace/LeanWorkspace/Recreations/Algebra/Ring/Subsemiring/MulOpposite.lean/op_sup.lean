import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem op_sup (S₁ S₂ : Subsemiring R) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op := Subsemiring.opEquiv.map_sup _ _

