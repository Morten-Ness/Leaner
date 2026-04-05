import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_one' {s : Set α} : s.mulIndicator (1 : α → M) = 1 := Set.mulIndicator_one M s

