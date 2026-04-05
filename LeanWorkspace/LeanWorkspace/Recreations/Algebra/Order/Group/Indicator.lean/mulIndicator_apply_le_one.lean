import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [Preorder M] [One M] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_apply_le_one (h : a ∈ s → f a ≤ 1) : mulIndicator s f a ≤ 1 := Set.mulIndicator_apply_le' h fun _ ↦ le_rfl

