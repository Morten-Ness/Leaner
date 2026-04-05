import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [Preorder M] [One M] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_mono (h : f ≤ g) : s.mulIndicator f ≤ s.mulIndicator g := fun _ ↦ Set.mulIndicator_le_mulIndicator (h _)

