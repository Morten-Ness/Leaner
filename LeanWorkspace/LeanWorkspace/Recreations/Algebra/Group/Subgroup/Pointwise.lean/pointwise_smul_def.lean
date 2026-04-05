import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

variable [Monoid α] [MulDistribMulAction α G]

theorem pointwise_smul_def {a : α} (S : Subgroup G) :
    a • S = S.map (MulDistribMulAction.toMonoidEnd _ _ a) := rfl

