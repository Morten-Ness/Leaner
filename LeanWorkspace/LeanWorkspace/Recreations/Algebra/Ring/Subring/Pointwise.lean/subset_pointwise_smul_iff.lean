import Mathlib

variable {M R : Type*}

variable [Group M] [Ring R] [MulSemiringAction M R]

theorem subset_pointwise_smul_iff {a : M} {S T : Subring R} : S ≤ a • T ↔ a⁻¹ • S ≤ T := subset_smul_set_iff

