import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*}

variable [GroupWithZero G₀] [Group G] [MulDistribMulAction G₀ G] {S T : Subgroup G} {a : G₀}

theorem le_pointwise_smul_iff₀ (ha : a ≠ 0) : S ≤ a • T ↔ a⁻¹ • S ≤ T := subset_smul_set_iff₀ ha

