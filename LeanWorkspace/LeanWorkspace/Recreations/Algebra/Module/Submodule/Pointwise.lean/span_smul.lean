import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable [Monoid α] [DistribMulAction α M] [SMulCommClass α R M]

theorem span_smul (a : α) (s : Set M) : span R (a • s) = a • span R s := Eq.symm (span_image _).symm

