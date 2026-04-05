import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [Group G] [DistribMulAction G A] {a : G}

theorem pointwise_smul_le_iff {S T : AddSubmonoid A} : a • S ≤ T ↔ S ≤ a⁻¹ • T := smul_set_subset_iff_subset_inv_smul_set

