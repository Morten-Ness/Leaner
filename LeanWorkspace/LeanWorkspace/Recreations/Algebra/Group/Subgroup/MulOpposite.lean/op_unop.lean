import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_unop (S : Subgroup Gᵐᵒᵖ) : S.unop.op = S := rfl

