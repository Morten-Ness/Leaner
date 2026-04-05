import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem unop_closure (s : Set Gᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  rw [← op_inj, op_unop, Subgroup.op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

