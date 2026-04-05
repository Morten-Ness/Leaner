import Mathlib

variable {F α β γ : Type*}

variable [Group α] {s t : Set α} {a b : α}

theorem preimage_mul_left_one' : (a⁻¹ * ·) ⁻¹' 1 = {a} := by simp

