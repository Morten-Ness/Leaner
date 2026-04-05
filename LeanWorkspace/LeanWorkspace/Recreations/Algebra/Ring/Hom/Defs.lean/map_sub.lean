import Mathlib

variable {F α β γ : Type*}

theorem map_sub [NonAssocRing α] [NonAssocRing β] (f : α →+* β) (x y : α) :
    f (x - y) = f x - f y := map_sub f x y

