import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem periodic_with_period_zero [AddZeroClass α] (f : α → β) : Function.Periodic f 0 := fun x => by
  rw [add_zero]

