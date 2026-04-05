import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [Preorder M] [One M] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_le_mulIndicator_of_subset (h : s ⊆ t) (hf : 1 ≤ f) :
    mulIndicator s f ≤ mulIndicator t f := fun _ ↦ Set.mulIndicator_le_mulIndicator_apply_of_subset h (hf _)

