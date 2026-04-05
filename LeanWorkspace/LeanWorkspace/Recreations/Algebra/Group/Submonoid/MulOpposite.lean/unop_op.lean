import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem unop_op (S : Submonoid M) : S.op.unop = S := rfl

