import Mathlib

variable {M R : Type*}

variable [GroupWithZero M] [Ring R] [MulSemiringAction M R]

theorem le_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) {S T : Subring R} : S ≤ a • T ↔ a⁻¹ • S ≤ T := subset_smul_set_iff₀ ha

