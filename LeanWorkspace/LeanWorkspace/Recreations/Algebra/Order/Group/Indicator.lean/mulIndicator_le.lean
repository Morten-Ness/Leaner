import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [Monoid M] [PartialOrder M] [CanonicallyOrderedMul M]

theorem mulIndicator_le {s : Set α} {f g : α → M} (hfg : ∀ a ∈ s, f a ≤ g a) :
    mulIndicator s f ≤ g := Set.mulIndicator_le' hfg fun _ _ ↦ one_le _

