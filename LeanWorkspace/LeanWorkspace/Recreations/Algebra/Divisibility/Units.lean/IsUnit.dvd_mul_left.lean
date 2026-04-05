import Mathlib

variable {α : Type*}

variable [CommMonoid α] {a b u : α}

theorem dvd_mul_left (hu : IsUnit u) : a ∣ u * b ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.dvd_mul_left

