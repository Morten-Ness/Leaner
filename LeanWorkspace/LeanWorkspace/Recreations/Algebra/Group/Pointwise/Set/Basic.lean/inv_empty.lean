import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} [Inv α] {s t : Set α} {a : α}

theorem inv_empty : (∅ : Set α)⁻¹ = ∅ := rfl

