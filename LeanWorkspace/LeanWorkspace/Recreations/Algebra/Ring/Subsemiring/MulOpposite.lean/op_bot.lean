import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem op_bot : (⊥ : Subsemiring R).op = ⊥ := Subsemiring.opEquiv.map_bot

