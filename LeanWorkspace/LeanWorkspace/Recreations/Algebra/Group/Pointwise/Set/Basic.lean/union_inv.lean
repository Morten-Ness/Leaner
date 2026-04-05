import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} [Inv α] {s t : Set α} {a : α}

theorem union_inv : (s ∪ t)⁻¹ = s⁻¹ ∪ t⁻¹ := preimage_union

