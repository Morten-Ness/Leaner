import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_of_mem (h : a ∈ s) (f : α → M) : Set.mulIndicator s f a = f a := if_pos h

