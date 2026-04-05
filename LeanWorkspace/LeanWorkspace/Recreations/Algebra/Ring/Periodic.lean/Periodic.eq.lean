import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.eq [AddZeroClass α] (h : Function.Periodic f c) : f c = f 0 := by
  simpa only [zero_add] using h 0

