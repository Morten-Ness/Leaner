import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*}

variable [Group G] [AddGroup A] [DistribMulAction G A] {S T : AddSubgroup A} {a : G} {x : A}

theorem pointwise_smul_le_pointwise_smul_iff : a • S ≤ a • T ↔ S ≤ T := smul_set_subset_smul_set_iff

