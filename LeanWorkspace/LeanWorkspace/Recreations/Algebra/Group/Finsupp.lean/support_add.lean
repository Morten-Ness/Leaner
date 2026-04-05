import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem support_add [DecidableEq ι] : (g₁ + g₂).support ⊆ g₁.support ∪ g₂.support := support_zipWith

