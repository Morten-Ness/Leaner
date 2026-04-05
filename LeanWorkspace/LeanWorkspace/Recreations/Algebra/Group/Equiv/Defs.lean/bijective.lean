import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem bijective (e : M ≃* N) : Function.Bijective e := EquivLike.bijective e

