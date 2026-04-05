import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem op_bot : (⊥ : Subring R).op = ⊥ := Subring.opEquiv.map_bot

