import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_empty' (f : α → M) : Set.mulIndicator (∅ : Set α) f = 1 := Set.mulIndicator_empty f

