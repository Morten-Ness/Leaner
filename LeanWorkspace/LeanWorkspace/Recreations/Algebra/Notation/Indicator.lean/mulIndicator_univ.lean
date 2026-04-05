import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_univ (f : α → M) : Set.mulIndicator (univ : Set α) f = f := Set.mulIndicator_eq_self.2 <| subset_univ _

