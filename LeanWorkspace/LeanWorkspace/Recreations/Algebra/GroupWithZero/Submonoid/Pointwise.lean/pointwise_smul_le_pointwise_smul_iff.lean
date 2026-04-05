import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [Group G] [DistribMulAction G A] {a : G}

theorem pointwise_smul_le_pointwise_smul_iff {S T : AddSubmonoid A} :
    a • S ≤ a • T ↔ S ≤ T := smul_set_subset_smul_set_iff

