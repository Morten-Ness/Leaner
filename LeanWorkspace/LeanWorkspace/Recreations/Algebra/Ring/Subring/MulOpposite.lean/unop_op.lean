import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem unop_op (S : Subring R) : S.op.unop = S := rfl

