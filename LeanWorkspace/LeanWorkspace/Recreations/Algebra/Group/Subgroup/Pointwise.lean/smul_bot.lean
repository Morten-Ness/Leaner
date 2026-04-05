import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

variable [Monoid α] [MulDistribMulAction α G]

theorem smul_bot (a : α) : a • (⊥ : Subgroup G) = ⊥ := map_bot _

