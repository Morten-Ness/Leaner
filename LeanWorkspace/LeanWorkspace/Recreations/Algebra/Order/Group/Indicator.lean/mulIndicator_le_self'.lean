import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [Preorder M] [One M] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_le_self' (hf : ∀ x ∉ s, 1 ≤ f x) : mulIndicator s f ≤ f := Set.mulIndicator_le' (fun _ _ ↦ le_rfl) hf

