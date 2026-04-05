import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

variable [Group α] [MulDistribMulAction α G]

theorem smul_inf (a : α) (S T : Subgroup G) : a • (S ⊓ T) = a • S ⊓ a • T := by
  simp [SetLike.ext_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]

