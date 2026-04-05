import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable [Monoid α] [DistribMulAction α M] [SMulCommClass α R M]

theorem pointwise_smul_toAddSubgroup {R M : Type*} [Ring R] [AddCommGroup M] [DistribMulAction α M]
    [Module R M] [SMulCommClass α R M] (a : α) (S : Submodule R M) :
    (a • S).toAddSubgroup = a • S.toAddSubgroup := rfl

