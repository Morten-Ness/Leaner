import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable [Monoid α] [DistribMulAction α M] [SMulCommClass α R M]

theorem smul_def (a : α) (S : Submodule R M) : a • S = span R (a • S : Set M) := by simp [← Submodule.smul_span]

