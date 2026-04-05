import Mathlib

variable {M R : Type*}

variable [Group M] [Semiring R] [MulSemiringAction M R]

theorem pointwise_smul_le_pointwise_smul_iff {a : M} {S T : Subsemiring R} :
    a • S ≤ a • T ↔ S ≤ T := smul_set_subset_smul_set_iff

