import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem symm_symm (f : M ≃* N) : f.symm.symm = f := rfl

