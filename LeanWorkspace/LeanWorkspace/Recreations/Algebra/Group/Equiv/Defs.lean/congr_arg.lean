import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem congr_arg {f : MulEquiv M N} {x x' : M} : x = x' → f x = f x' := DFunLike.congr_arg f

