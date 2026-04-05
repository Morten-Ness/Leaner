import Mathlib

variable {M R : Type*}

variable [Group M] [Ring R] [MulSemiringAction M R]

theorem pointwise_smul_subset_iff {a : M} {S T : Subring R} : a • S ≤ T ↔ S ≤ a⁻¹ • T := smul_set_subset_iff_subset_inv_smul_set

