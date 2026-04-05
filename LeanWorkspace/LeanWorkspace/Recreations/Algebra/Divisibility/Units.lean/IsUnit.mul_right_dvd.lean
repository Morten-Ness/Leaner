import Mathlib

variable {α : Type*}

variable [Monoid α] {a b u : α}

theorem mul_right_dvd (hu : IsUnit u) : a * u ∣ b ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.mul_right_dvd

