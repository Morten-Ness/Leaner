import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem congr_fun {f g : MulEquiv M N} (h : f = g) (x : M) : f x = g x := DFunLike.congr_fun h x

