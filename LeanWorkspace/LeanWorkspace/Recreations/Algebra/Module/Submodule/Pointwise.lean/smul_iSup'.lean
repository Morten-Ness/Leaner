import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable [Monoid α] [DistribMulAction α M] [SMulCommClass α R M]

theorem smul_iSup' (a : α) {ι : Sort*} (f : ι → Submodule R M) :
    a • ⨆ i, f i = ⨆ i, a • f i := map_iSup _ _

