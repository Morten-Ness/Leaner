import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.neg [AddGroup α] (h : Function.Periodic f c) : Function.Periodic f (-c) := by
  simpa only [sub_eq_add_neg, Function.Periodic] using h.sub_eq

