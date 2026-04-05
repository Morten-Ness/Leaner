import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G}

theorem stabilizer_subgroup_op (s : Subgroup Gᵐᵒᵖ) : stabilizer G (s : Set Gᵐᵒᵖ) = s.unop := by
  simp_rw [SetLike.ext_iff, MulAction.mem_stabilizer_set]
  refine fun a ↦ ⟨fun h ↦ ?_, fun ha b ↦ s.mul_mem_cancel_right ha⟩
  have : 1 * MulOpposite.op a ∈ s := (h 1).2 s.one_mem
  simpa only [op_smul_eq_mul, SetLike.mem_coe, one_mul] using this

