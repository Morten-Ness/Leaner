import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem symm_comp_self (e : M ≃* N) : e.symm ∘ e = id := funext MulEquiv.symm_apply_apply e

