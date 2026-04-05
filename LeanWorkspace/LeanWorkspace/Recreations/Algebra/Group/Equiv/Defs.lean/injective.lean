import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem injective (e : M ≃* N) : Function.Injective e := EquivLike.injective e

