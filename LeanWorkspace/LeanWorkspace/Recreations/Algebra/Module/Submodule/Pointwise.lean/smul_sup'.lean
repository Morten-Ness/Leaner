import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable [Monoid α] [DistribMulAction α M] [SMulCommClass α R M]

theorem smul_sup' (a : α) (S T : Submodule R M) : a • (S ⊔ T) = a • S ⊔ a • T := map_sup _ _ _

