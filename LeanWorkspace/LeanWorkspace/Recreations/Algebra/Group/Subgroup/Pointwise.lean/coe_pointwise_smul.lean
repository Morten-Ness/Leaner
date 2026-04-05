import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

variable [Monoid α] [MulDistribMulAction α G]

theorem coe_pointwise_smul (a : α) (S : Subgroup G) : ↑(a • S) = a • (S : Set G) := rfl

