import Mathlib

variable {α : Type*} {s t : Set α} {a : α}

theorem star_preimage [Star α] : Star.star ⁻¹' s = s⋆ := rfl

