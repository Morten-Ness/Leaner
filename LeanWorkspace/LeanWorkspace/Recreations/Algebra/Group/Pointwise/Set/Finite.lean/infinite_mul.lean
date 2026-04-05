import Mathlib

variable {F α β γ : Type*}

variable [Mul α] [IsLeftCancelMul α] [IsRightCancelMul α] {s t : Set α}

theorem infinite_mul : (s * t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty := infinite_image2 (fun _ _ => (mul_left_injective _).injOn) fun _ _ => (mul_right_injective _).injOn

