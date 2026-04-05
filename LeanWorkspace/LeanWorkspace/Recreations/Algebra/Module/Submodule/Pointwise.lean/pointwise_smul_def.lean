import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable [Monoid α] [DistribMulAction α M] [SMulCommClass α R M]

theorem pointwise_smul_def {a : α} {S : Submodule R M} :
    a • S = S.map (DistribSMul.toLinearMap R M a) := rfl

