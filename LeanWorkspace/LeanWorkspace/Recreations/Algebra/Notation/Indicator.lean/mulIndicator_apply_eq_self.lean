import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_apply_eq_self : s.mulIndicator f a = f a ↔ a ∉ s → f a = 1 := letI := Classical.dec (a ∈ s)
  ite_eq_left_iff.trans (by rw [@eq_comm _ (f a)])

