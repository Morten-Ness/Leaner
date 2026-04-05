import Mathlib

variable {M R : Type*}

variable [GroupWithZero M] [Semiring R] [MulSemiringAction M R]

theorem pointwise_smul_le_iff₀ {a : M} (ha : a ≠ 0) {S T : Subsemiring R} :
    a • S ≤ T ↔ S ≤ a⁻¹ • T := smul_set_subset_iff₀ ha

