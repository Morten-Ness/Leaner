import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable [Monoid α] [MulDistribMulAction α M]

theorem smul_sup (a : α) (S T : Submonoid M) : a • (S ⊔ T) = a • S ⊔ a • T := map_sup _ _ _

