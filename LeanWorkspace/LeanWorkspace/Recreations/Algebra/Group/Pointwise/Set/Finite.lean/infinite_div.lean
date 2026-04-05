import Mathlib

variable {F α β γ : Type*}

variable [Group α] {s t : Set α}

theorem infinite_div : (s / t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty := infinite_image2 (fun _ _ ↦ div_left_injective.injOn) fun _ _ ↦ div_right_injective.injOn

