import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem eqOn_mulIndicator : EqOn (Set.mulIndicator s f) f s := fun _ hx => Set.mulIndicator_of_mem hx f

