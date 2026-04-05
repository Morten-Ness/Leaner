import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

variable [Monoid α] [MulDistribMulAction α G]

theorem smul_mem_pointwise_smul (m : G) (a : α) (S : Subgroup G) : m ∈ S → a • m ∈ a • S := (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set G))

