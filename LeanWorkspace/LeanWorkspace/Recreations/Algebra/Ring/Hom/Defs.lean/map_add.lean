import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β)

theorem map_add (f : α →+* β) : ∀ a b, f (a + b) = f a + f b := map_add f

