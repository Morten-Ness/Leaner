import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem self_comp_symm (e : M ≃* N) : e ∘ e.symm = id := funext MulEquiv.apply_symm_apply e

