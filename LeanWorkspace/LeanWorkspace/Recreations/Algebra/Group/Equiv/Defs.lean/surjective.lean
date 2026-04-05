import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem surjective (e : M ≃* N) : Function.Surjective e := EquivLike.surjective e

