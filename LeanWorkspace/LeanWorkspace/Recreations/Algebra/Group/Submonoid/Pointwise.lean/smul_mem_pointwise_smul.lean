import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable [Monoid α] [MulDistribMulAction α M]

theorem smul_mem_pointwise_smul (m : M) (a : α) (S : Submonoid M) : m ∈ S → a • m ∈ a • S := (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set M))

