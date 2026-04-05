import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_empty (f : α → M) : Set.mulIndicator (∅ : Set α) f = fun _ => 1 := Set.mulIndicator_eq_one.2 <| disjoint_empty _

