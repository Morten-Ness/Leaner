import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable [Monoid α] [MulDistribMulAction α M]

theorem coe_pointwise_smul (a : α) (S : Submonoid M) : ↑(a • S) = a • (S : Set M) := rfl

