import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem unop_op (S : Subsemiring R) : S.op.unop = S := rfl

