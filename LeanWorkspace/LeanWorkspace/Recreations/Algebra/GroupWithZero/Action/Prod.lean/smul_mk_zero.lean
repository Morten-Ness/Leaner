import Mathlib

variable {M N α β : Type*}

variable [SMul M α] [SMul M β]

theorem smul_mk_zero {β : Type*} [Monoid M] [AddMonoid β] [DistribMulAction M β] (a : M) (b : α) :
    a • (b, (0 : β)) = (a • b, 0) := by rw [Prod.smul_mk, smul_zero]

