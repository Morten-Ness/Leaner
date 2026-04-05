import Mathlib

variable {M R : Type*}

variable [Monoid M] [Ring R] [MulSemiringAction M R]

theorem mem_smul_pointwise_iff_exists (m : M) (r : R) (S : Subring R) :
    r ∈ m • S ↔ ∃ s : R, s ∈ S ∧ m • s = r := (Set.mem_smul_set : r ∈ m • (S : Set R) ↔ _)

