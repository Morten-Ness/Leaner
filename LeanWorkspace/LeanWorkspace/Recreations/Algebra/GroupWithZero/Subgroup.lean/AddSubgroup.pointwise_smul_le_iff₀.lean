import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*}

variable [GroupWithZero G₀] [AddGroup A] [DistribMulAction G₀ A] {S T : AddSubgroup A} {a : G₀}

theorem pointwise_smul_le_iff₀ (ha : a ≠ 0) : a • S ≤ T ↔ S ≤ a⁻¹ • T := smul_set_subset_iff₀ ha

