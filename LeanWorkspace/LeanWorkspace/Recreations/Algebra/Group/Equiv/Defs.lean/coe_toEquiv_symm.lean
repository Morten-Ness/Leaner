import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem coe_toEquiv_symm (f : M ≃* N) : ((f : M ≃ N).symm : N → M) = f.symm := rfl

