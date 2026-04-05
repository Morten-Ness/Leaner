import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β)

theorem congr_fun {f g : α →+* β} (h : f = g) (x : α) : f x = g x := DFunLike.congr_fun h x

