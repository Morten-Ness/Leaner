import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_normalizer (H : Subgroup G) : (normalizer H : Subgroup G).op = normalizer H.op := by
  ext x
  rw [Subgroup.mem_op, mem_normalizer_iff', mem_normalizer_iff']
  simp [iff_comm]

