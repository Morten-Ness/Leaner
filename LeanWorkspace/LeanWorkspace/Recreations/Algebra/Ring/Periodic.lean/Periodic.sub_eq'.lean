import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.sub_eq' [SubtractionCommMonoid α] (h : Function.Periodic f c) : f (c - x) = f (-x) := by
  simpa only [sub_eq_neg_add] using h (-x)

