import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*}

variable [Group G] [AddGroup A] [DistribMulAction G A] {S T : AddSubgroup A} {a : G} {x : A}

theorem le_pointwise_smul_iff : S ≤ a • T ↔ a⁻¹ • S ≤ T := subset_smul_set_iff

