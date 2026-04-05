import Mathlib

variable {M R : Type*}

variable [GroupWithZero M] [Semiring R] [MulSemiringAction M R]

theorem smul_mem_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) (S : Subsemiring R) (x : R) :
    a • x ∈ a • S ↔ x ∈ S := smul_mem_smul_set_iff₀ ha (S : Set R) x

