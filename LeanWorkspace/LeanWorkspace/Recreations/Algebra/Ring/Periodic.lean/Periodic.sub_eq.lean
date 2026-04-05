import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.sub_eq [AddGroup α] (h : Function.Periodic f c) (x : α) : f (x - c) = f x := by
  simpa only [sub_add_cancel] using (h (x - c)).symm

