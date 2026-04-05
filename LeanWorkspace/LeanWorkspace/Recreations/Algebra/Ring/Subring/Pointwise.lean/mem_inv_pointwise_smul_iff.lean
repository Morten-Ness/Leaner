import Mathlib

variable {M R : Type*}

variable [Group M] [Ring R] [MulSemiringAction M R]

theorem mem_inv_pointwise_smul_iff {a : M} {S : Subring R} {x : R} : x ∈ a⁻¹ • S ↔ a • x ∈ S := mem_inv_smul_set_iff

