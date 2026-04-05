import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable [Group α] [MulDistribMulAction α M]

theorem subset_pointwise_smul_iff {a : α} {S T : Submonoid M} : S ≤ a • T ↔ a⁻¹ • S ≤ T := subset_smul_set_iff

