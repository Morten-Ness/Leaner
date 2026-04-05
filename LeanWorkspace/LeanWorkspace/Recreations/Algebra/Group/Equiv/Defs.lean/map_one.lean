import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass N] [MulOneClass P]

theorem map_one (h : M ≃* N) : h 1 = 1 := map_one h

