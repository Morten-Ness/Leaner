import Mathlib

variable {M R : Type*}

variable [Group M] [Semiring R] [MulSemiringAction M R]

theorem subset_pointwise_smul_iff {a : M} {S T : Subsemiring R} : S ≤ a • T ↔ a⁻¹ • S ≤ T := subset_smul_set_iff

