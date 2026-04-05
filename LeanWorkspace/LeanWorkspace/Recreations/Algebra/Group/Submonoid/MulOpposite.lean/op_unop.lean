import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_unop (S : Submonoid Mᵐᵒᵖ) : S.unop.op = S := rfl

