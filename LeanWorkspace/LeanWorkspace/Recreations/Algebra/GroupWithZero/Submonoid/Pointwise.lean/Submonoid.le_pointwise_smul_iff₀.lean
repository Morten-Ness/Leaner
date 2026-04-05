import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [GroupWithZero G₀] [MulDistribMulAction G₀ M] {a : G₀}

theorem le_pointwise_smul_iff₀ (ha : a ≠ 0) {S T : Submonoid M} : S ≤ a • T ↔ a⁻¹ • S ≤ T := subset_smul_set_iff₀ ha

