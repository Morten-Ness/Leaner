import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*}

variable [GroupWithZero G₀] [AddGroup A] [DistribMulAction G₀ A] {S T : AddSubgroup A} {a : G₀}

theorem le_pointwise_smul_iff₀ (ha : a ≠ 0) : S ≤ a • T ↔ a⁻¹ • S ≤ T := subset_smul_set_iff₀ ha

