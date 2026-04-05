import Mathlib

variable {α : Type*}

variable [Monoid α] {a b u : α}

theorem dvd_mul_right (hu : IsUnit u) : a ∣ b * u ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.dvd_mul_right

