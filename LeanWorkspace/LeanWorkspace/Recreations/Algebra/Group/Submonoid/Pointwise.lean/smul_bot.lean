import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable [Monoid α] [MulDistribMulAction α M]

theorem smul_bot (a : α) : a • (⊥ : Submonoid M) = ⊥ := map_bot _

