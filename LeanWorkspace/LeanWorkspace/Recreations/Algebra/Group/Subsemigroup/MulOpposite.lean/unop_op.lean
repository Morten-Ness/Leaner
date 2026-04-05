import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_op (S : Subsemigroup M) : S.op.unop = S := rfl

