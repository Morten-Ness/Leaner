import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem symm_apply_apply (e : M ≃* N) (x : M) : e.symm (e x) = x := e.toEquiv.symm_apply_apply x

