import Mathlib

variable {F α β γ : Type*}

variable [Group α] {s t : Set α} {a b : α}

theorem preimage_mul_right_one : (· * b) ⁻¹' 1 = {b⁻¹} := by
  rw [← Set.image_mul_right', Set.image_one, one_mul]

