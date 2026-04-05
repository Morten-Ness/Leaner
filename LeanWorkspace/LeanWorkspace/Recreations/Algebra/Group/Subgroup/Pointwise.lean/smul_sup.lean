import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

variable [Monoid α] [MulDistribMulAction α G]

theorem smul_sup (a : α) (S T : Subgroup G) : a • (S ⊔ T) = a • S ⊔ a • T := map_sup _ _ _

