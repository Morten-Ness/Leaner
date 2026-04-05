import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_rel_mulIndicator {r : M → M → Prop} (h1 : r 1 1) (ha : a ∈ s → r (f a) (g a)) :
    r (Set.mulIndicator s f a) (Set.mulIndicator s g a) := by
  simp only [Set.mulIndicator]
  split_ifs with has
  exacts [ha has, h1]

