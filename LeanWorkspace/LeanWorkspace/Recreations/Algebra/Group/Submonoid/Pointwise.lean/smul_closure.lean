import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable [Monoid α] [MulDistribMulAction α M]

theorem smul_closure (a : α) (s : Set M) : a • closure s = closure (a • s) := MonoidHom.map_mclosure _ _

