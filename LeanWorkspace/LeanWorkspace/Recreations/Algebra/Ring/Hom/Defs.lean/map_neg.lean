import Mathlib

variable {F α β γ : Type*}

theorem map_neg [NonAssocRing α] [NonAssocRing β] (f : α →+* β) (x : α) : f (-x) = -f x := map_neg f x

