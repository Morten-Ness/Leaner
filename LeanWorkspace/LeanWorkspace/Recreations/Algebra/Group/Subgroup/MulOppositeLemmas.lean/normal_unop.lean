import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem normal_unop {H : Subgroup Gᵐᵒᵖ} : H.unop.Normal ↔ H.Normal := by
  rw [← Subgroup.normal_op, op_unop]

