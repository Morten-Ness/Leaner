import Mathlib

variable {M N α β : Type*}

variable [SMul M α] [SMul M β]

theorem smul_zero_mk {α : Type*} [Monoid M] [AddMonoid α] [DistribMulAction M α] (a : M) (c : β) :
    a • ((0 : α), c) = (0, a • c) := by rw [Prod.smul_mk, smul_zero]

