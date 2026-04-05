import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [DistribMulAction M A]

theorem smul_mem_pointwise_smul (a : A) (m : M) (S : AddSubmonoid A) : a ∈ S → m • a ∈ m • S := (Set.smul_mem_smul_set : _ → _ ∈ m • (S : Set A))

