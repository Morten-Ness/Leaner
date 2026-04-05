import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem apply_symm_apply (e : M ≃* N) (y : N) : e (e.symm y) = y := e.toEquiv.apply_symm_apply y

