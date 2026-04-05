import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [LE M] [One M] {s : Set α} {f g : α → M} {a : α} {y : M}

theorem le_mulIndicator (hfg : ∀ a ∈ s, f a ≤ g a) (hf : ∀ a ∉ s, f a ≤ 1) :
    f ≤ mulIndicator s g := fun _ ↦ Set.le_mulIndicator_apply (hfg _) (hf _)

