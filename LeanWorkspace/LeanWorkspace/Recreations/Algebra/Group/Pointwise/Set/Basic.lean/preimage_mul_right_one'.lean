import Mathlib

variable {F α β γ : Type*}

variable [Group α] {s t : Set α} {a b : α}

theorem preimage_mul_right_one' : (· * b⁻¹) ⁻¹' 1 = {b} := by simp

