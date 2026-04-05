import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem normal_op {H : Subgroup G} : H.op.Normal ↔ H.Normal := by
  simp only [← normalizer_eq_top_iff, ← op_normalizer, Subgroup.op_eq_top]

