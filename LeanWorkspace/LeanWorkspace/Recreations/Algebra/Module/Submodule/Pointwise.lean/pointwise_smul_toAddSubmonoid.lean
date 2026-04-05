import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable [Monoid α] [DistribMulAction α M] [SMulCommClass α R M]

theorem pointwise_smul_toAddSubmonoid (a : α) (S : Submodule R M) :
    (a • S).toAddSubmonoid = a • S.toAddSubmonoid := rfl

