import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_eq_one' : Set.mulIndicator s f = 1 ↔ Disjoint (mulSupport f) s := Set.mulIndicator_eq_one

