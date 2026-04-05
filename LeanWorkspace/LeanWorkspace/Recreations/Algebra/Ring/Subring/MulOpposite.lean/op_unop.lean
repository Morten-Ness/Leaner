import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem op_unop (S : Subring Rᵐᵒᵖ) : S.unop.op = S := rfl

