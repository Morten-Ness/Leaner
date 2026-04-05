import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G}

theorem stabilizer_op_subgroup (s : Subgroup G) : stabilizer Gᵐᵒᵖ (s : Set G) = s.op := by
  simp_rw [SetLike.ext_iff, MulAction.mem_stabilizer_set]
  simp only [smul_eq_mul_unop, SetLike.mem_coe, Subgroup.mem_op, «forall», unop_op]
  refine fun a ↦ ⟨fun h ↦ ?_, fun ha b ↦ s.mul_mem_cancel_right ha⟩
  simpa only [op_smul_eq_mul, SetLike.mem_coe, one_mul] using (h 1).2 s.one_mem

