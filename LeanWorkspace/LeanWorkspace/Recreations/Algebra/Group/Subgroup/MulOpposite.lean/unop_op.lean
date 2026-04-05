import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem unop_op (S : Subgroup G) : S.op.unop = S := rfl

