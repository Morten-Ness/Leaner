import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem op_top : (⊤ : Subsemiring R).op = ⊤ := rfl

