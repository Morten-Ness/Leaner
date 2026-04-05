import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [Monoid M] [PartialOrder M] [CanonicallyOrderedMul M]

theorem mulIndicator_le_self (s : Set α) (f : α → M) : mulIndicator s f ≤ f := Set.mulIndicator_le_self' fun _ _ ↦ one_le _

