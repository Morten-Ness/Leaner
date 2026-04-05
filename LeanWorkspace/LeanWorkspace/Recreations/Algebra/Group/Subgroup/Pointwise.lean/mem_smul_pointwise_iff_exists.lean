import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

variable [Monoid α] [MulDistribMulAction α G]

theorem mem_smul_pointwise_iff_exists (m : G) (a : α) (S : Subgroup G) :
    m ∈ a • S ↔ ∃ s : G, s ∈ S ∧ a • s = m := (Set.mem_smul_set : m ∈ a • (S : Set G) ↔ _)

