import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

variable [Group α] [MulDistribMulAction α G]

theorem pointwise_smul_le_pointwise_smul_iff {a : α} {S T : Subgroup G} : a • S ≤ a • T ↔ S ≤ T := smul_set_subset_smul_set_iff

