import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem op_top : (⊤ : Subring R).op = ⊤ := rfl

