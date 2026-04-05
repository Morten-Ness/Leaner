import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_comp_of_one {g : M → N} (hg : g 1 = 1) :
    Set.mulIndicator s (g ∘ f) = g ∘ Set.mulIndicator s f := by
  funext
  simp only [Set.mulIndicator]
  split_ifs <;> simp [*]

