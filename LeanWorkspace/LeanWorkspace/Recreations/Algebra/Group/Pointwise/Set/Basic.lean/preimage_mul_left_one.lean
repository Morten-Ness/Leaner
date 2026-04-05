import Mathlib

variable {F α β γ : Type*}

variable [Group α] {s t : Set α} {a b : α}

theorem preimage_mul_left_one : (a * ·) ⁻¹' 1 = {a⁻¹} := by
  rw [← Set.image_mul_left', Set.image_one, mul_one]

