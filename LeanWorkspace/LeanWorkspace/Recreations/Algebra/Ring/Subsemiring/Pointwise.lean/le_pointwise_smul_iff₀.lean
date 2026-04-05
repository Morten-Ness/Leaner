import Mathlib

variable {M R : Type*}

variable [GroupWithZero M] [Semiring R] [MulSemiringAction M R]

theorem le_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) {S T : Subsemiring R} :
    S ≤ a • T ↔ a⁻¹ • S ≤ T := subset_smul_set_iff₀ ha

