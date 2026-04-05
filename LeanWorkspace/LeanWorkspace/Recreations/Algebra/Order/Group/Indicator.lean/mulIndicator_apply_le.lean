import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [Monoid M] [PartialOrder M] [CanonicallyOrderedMul M]

theorem mulIndicator_apply_le {a : α} {s : Set α} {f g : α → M} (hfg : a ∈ s → f a ≤ g a) :
    mulIndicator s f a ≤ g a := Set.mulIndicator_apply_le' hfg fun _ ↦ one_le _

