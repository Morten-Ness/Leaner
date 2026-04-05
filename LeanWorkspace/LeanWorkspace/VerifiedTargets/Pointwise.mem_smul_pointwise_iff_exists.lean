import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [DistribMulAction M A]

theorem mem_smul_pointwise_iff_exists (a : A) (m : M) (S : AddSubmonoid A) :
    a ∈ m • S ↔ ∃ s : A, s ∈ S ∧ m • s = a := (Set.mem_smul_set : a ∈ m • (S : Set A) ↔ _)

