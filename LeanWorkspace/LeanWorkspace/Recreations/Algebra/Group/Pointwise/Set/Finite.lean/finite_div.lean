import Mathlib

variable {F α β γ : Type*}

variable [Group α] {s t : Set α}

theorem finite_div : (s / t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅ := finite_image2 (fun _ _ ↦ div_left_injective.injOn) fun _ _ ↦ div_right_injective.injOn

