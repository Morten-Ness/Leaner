import Mathlib

variable {M R : Type*}

variable [Group M] [Ring R] [MulSemiringAction M R]

theorem mem_pointwise_smul_iff_inv_smul_mem {a : M} {S : Subring R} {x : R} :
    x ∈ a • S ↔ a⁻¹ • x ∈ S := mem_smul_set_iff_inv_smul_mem

