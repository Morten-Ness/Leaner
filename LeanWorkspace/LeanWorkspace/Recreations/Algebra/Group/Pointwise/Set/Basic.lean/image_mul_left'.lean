import Mathlib

variable {F α β γ : Type*}

variable [Group α] {s t : Set α} {a b : α}

theorem image_mul_left' : (a⁻¹ * ·) '' t = (a * ·) ⁻¹' t := by simp

