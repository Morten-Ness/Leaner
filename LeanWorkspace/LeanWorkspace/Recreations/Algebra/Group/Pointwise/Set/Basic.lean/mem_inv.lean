import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} [Inv α] {s t : Set α} {a : α}

theorem mem_inv : a ∈ s⁻¹ ↔ a⁻¹ ∈ s := Iff.rfl

