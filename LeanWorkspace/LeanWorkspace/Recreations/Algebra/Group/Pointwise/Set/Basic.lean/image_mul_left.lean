import Mathlib

variable {F α β γ : Type*}

variable [Group α] {s t : Set α} {a b : α}

theorem image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t := by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp

