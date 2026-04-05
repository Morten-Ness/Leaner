import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*}

variable [Group G] [AddGroup A] [DistribMulAction G A] {S T : AddSubgroup A} {a : G} {x : A}

theorem pointwise_smul_le_iff : a • S ≤ T ↔ S ≤ a⁻¹ • T := smul_set_subset_iff_subset_inv_smul_set

