import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem op_unop (S : Subsemiring Rᵐᵒᵖ) : S.unop.op = S := rfl

