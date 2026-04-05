import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [Group G] [DistribMulAction G A] {a : G}

theorem le_pointwise_smul_iff {S T : AddSubmonoid A} : S ≤ a • T ↔ a⁻¹ • S ≤ T := subset_smul_set_iff

