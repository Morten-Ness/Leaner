import Mathlib

variable {M R : Type*}

variable [Monoid M] [Semiring R] [MulSemiringAction M R]

theorem smul_mem_pointwise_smul (m : M) (r : R) (S : Subsemiring R) : r ∈ S → m • r ∈ m • S := (Set.smul_mem_smul_set : _ → _ ∈ m • (S : Set R))

