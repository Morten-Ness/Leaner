import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem ext {f g : MulEquiv M N} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

