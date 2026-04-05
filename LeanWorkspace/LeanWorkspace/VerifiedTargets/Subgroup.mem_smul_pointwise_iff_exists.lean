import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*}

variable [Monoid M] [AddGroup A] [DistribMulAction M A] {a : M}

theorem mem_smul_pointwise_iff_exists (m : A) (a : M) (S : AddSubgroup A) :
    m ∈ a • S ↔ ∃ s : A, s ∈ S ∧ a • s = m := (Set.mem_smul_set : m ∈ a • (S : Set A) ↔ _)

