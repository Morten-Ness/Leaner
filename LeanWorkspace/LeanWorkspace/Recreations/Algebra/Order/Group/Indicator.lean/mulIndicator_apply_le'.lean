import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [LE M] [One M] {s : Set α} {f g : α → M} {a : α} {y : M}

theorem mulIndicator_apply_le' (hfg : a ∈ s → f a ≤ y) (hg : a ∉ s → 1 ≤ y) :
    mulIndicator s f a ≤ y := by
  by_cases ha : a ∈ s
  · simpa [ha] using hfg ha
  · simpa [ha] using hg ha

