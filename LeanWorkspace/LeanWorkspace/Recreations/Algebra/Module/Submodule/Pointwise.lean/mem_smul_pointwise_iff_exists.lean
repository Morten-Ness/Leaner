import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable [Monoid α] [DistribMulAction α M] [SMulCommClass α R M]

theorem mem_smul_pointwise_iff_exists (m : M) (a : α) (S : Submodule R M) :
    m ∈ a • S ↔ ∃ b ∈ S, a • b = m := Set.mem_smul_set

