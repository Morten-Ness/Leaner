import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [Preorder M] [One M] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_le_mulIndicator (h : f a ≤ g a) : mulIndicator s f a ≤ mulIndicator s g a := mulIndicator_rel_mulIndicator le_rfl fun _ ↦ h

