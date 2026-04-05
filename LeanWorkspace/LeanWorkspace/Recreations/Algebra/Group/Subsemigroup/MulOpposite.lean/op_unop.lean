import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem op_unop (S : Subsemigroup Mᵐᵒᵖ) : S.unop.op = S := rfl

