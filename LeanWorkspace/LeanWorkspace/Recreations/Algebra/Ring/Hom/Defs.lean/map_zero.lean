import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β)

theorem map_zero (f : α →+* β) : f 0 = 0 := map_zero f

