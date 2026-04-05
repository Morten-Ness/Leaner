import Mathlib

variable {F α β γ : Type*}

variable [Group α] {s t : Set α} {a b : α}

theorem preimage_mul_right_singleton : (· * a) ⁻¹' {b} = {b * a⁻¹} := by
  rw [← Set.image_mul_right', image_singleton]

