import Mathlib

variable {α : Type*}

variable [CommMonoid α] {a b u : α}

theorem mul_left_dvd (hu : IsUnit u) : u * a ∣ b ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.mul_left_dvd

