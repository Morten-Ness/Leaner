import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable [Monoid α] [DistribMulAction α M] [SMulCommClass α R M]

theorem smul_mem_pointwise_smul (m : M) (a : α) (S : Submodule R M) : m ∈ S → a • m ∈ a • S := (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set M))

