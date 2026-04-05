import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem invFun_eq_symm {f : M ≃* N} : f.invFun = f.symm := rfl

