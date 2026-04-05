import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

variable [Monoid α] [MulDistribMulAction α G]

theorem pointwise_smul_toSubmonoid (a : α) (S : Subgroup G) :
    (a • S).toSubmonoid = a • S.toSubmonoid := rfl

