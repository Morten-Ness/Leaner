import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [LE M] [One M] {s : Set α} {f g : α → M} {a : α} {y : M}

theorem mulIndicator_le' (hfg : ∀ a ∈ s, f a ≤ g a) (hg : ∀ a, a ∉ s → 1 ≤ g a) :
    mulIndicator s f ≤ g := fun _ ↦ Set.mulIndicator_apply_le' (hfg _) (hg _)

