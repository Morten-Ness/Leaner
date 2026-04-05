import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [GroupWithZero G₀] [MulDistribMulAction G₀ M] {a : G₀}

theorem pointwise_smul_le_pointwise_smul_iff₀ (ha : a ≠ 0) {S T : Submonoid M} :
    a • S ≤ a • T ↔ S ≤ T := smul_set_subset_smul_set_iff₀ ha

