import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_comp_right {s : Set α} (f : β → α) {g : α → M} {x : β} :
    Set.mulIndicator (f ⁻¹' s) (g ∘ f) x = Set.mulIndicator s g (f x) := by
  tauto

