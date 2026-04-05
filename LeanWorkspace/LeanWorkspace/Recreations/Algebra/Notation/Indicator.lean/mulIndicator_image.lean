import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_image {s : Set α} {f : β → M} {g : α → β} (hg : Function.Injective g) {x : α} :
    Set.mulIndicator (g '' s) f (g x) = Set.mulIndicator s (f ∘ g) x := by
  rw [← Set.mulIndicator_comp_right, preimage_image_eq _ hg]

