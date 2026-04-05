import Mathlib

variable {F α β γ : Type*}

variable [Group α] {s t : Set α} {a b : α}

theorem preimage_mul_left_singleton : (a * ·) ⁻¹' {b} = {a⁻¹ * b} := by
  rw [← Set.image_mul_left', image_singleton]

