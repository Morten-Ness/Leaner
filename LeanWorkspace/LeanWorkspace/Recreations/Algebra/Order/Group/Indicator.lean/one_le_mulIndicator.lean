import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [Preorder M] [One M] {s t : Set α} {f g : α → M} {a : α}

theorem one_le_mulIndicator (h : ∀ a ∈ s, 1 ≤ f a) (a : α) : 1 ≤ mulIndicator s f a := Set.one_le_mulIndicator_apply (h a)

