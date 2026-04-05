import Mathlib

variable {F α β γ : Type*}

variable [Mul α] [IsLeftCancelMul α] [IsRightCancelMul α] {s t : Set α}

theorem finite_mul : (s * t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅ := finite_image2 (fun _ _ ↦ (mul_left_injective _).injOn) fun _ _ ↦ (mul_right_injective _).injOn

