import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem unop_normalizer (H : Subgroup Gᵐᵒᵖ) :
    (normalizer H).unop = normalizer (H.unop : Set G) := by
  rw [← Subgroup.op_inj, Subgroup.op_unop, Subgroup.op_normalizer, Subgroup.op_unop]

