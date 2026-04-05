import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β)

theorem congr_arg (f : α →+* β) {x y : α} (h : x = y) : f x = f y := DFunLike.congr_arg f h

