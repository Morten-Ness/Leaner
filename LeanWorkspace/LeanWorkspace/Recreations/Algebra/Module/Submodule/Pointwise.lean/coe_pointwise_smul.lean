import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable [Monoid α] [DistribMulAction α M] [SMulCommClass α R M]

theorem coe_pointwise_smul (a : α) (S : Submodule R M) : ↑(a • S) = a • (S : Set M) := rfl

