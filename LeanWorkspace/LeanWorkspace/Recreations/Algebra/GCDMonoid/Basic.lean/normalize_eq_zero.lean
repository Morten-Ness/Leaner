import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [NormalizationMonoid α]

theorem normalize_eq_zero {x : α} : normalize x = 0 ↔ x = 0 := ⟨fun hx => (associated_zero_iff_eq_zero x).1 <| hx ▸ associated_normalize _, by
    rintro rfl; exact normalize_zero⟩

