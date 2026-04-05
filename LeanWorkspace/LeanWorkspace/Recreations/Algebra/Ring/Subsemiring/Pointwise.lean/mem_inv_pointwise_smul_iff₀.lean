import Mathlib

variable {M R : Type*}

variable [GroupWithZero M] [Semiring R] [MulSemiringAction M R]

theorem mem_inv_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) (S : Subsemiring R) (x : R) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S := mem_inv_smul_set_iff₀ ha (S : Set R) x

