import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

theorem toSubsemigroup_injective : (toSubsemigroup : Submonoid M → Subsemigroup M).Injective := fun ⟨s, hs⟩ ⟨t, ht⟩ ↦ by congr!

