import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_apply (s : Set α) (f : α → M) (a : α) [Decidable (a ∈ s)] :
    Set.mulIndicator s f a = if a ∈ s then f a else 1 := by
  unfold Set.mulIndicator
  congr

