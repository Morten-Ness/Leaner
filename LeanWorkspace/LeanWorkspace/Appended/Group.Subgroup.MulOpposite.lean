import Mathlib

section

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_normalizer (H : Subgroup G) : (normalizer H : Subgroup G).op = normalizer H.op := by
  ext x
  rw [Subgroup.mem_op, mem_normalizer_iff', mem_normalizer_iff']
  simp [iff_comm]

end

section

variable {ι : Sort*} {G : Type*} [Group G]

theorem unop_normalizer (H : Subgroup Gᵐᵒᵖ) :
    (normalizer H).unop = normalizer (H.unop : Set G) := by
  rw [← Subgroup.op_inj, Subgroup.op_unop, Subgroup.op_normalizer, Subgroup.op_unop]

end
