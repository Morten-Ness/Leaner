import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [GroupWithZero G₀] [DistribMulAction G₀ A] {S T : AddSubmonoid A} {a : G₀}

theorem le_pointwise_smul_iff₀ (ha : a ≠ 0) : S ≤ a • T ↔ a⁻¹ • S ≤ T := subset_smul_set_iff₀ ha

