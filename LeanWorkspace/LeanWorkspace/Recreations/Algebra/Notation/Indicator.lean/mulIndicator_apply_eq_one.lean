import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_apply_eq_one : Set.mulIndicator s f a = 1 ↔ a ∈ s → f a = 1 := letI := Classical.dec (a ∈ s)
  ite_eq_right_iff

