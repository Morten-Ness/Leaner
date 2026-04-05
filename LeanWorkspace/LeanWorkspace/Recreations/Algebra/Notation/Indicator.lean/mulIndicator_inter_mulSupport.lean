import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_inter_mulSupport (s : Set α) (f : α → M) :
    Set.mulIndicator (s ∩ mulSupport f) f = Set.mulIndicator s f := by
  rw [← Set.mulIndicator_mulIndicator, Set.mulIndicator_mulSupport]

