import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [GroupWithZero G₀] [MulDistribMulAction G₀ M] {a : G₀}

theorem pointwise_smul_le_iff₀ (ha : a ≠ 0) {S T : Submonoid M} : a • S ≤ T ↔ S ≤ a⁻¹ • T := smul_set_subset_iff₀ ha

