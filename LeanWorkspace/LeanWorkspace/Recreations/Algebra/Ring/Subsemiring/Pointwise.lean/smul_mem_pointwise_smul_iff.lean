import Mathlib

variable {M R : Type*}

variable [Group M] [Semiring R] [MulSemiringAction M R]

theorem smul_mem_pointwise_smul_iff {a : M} {S : Subsemiring R} {x : R} : a • x ∈ a • S ↔ x ∈ S := smul_mem_smul_set_iff

