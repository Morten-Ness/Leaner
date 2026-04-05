import Mathlib

variable {M R : Type*}

variable [GroupWithZero M] [Semiring R] [MulSemiringAction M R]

theorem mem_pointwise_smul_iff_inv_smul_mem₀ {a : M} (ha : a ≠ 0) (S : Subsemiring R) (x : R) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S := mem_smul_set_iff_inv_smul_mem₀ ha (S : Set R) x

