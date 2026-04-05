import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem eq_symm_apply (e : M ≃* N) {x y} : y = e.symm x ↔ e y = x := e.toEquiv.eq_symm_apply

