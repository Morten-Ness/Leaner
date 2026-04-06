import Mathlib

variable {α : Type*}

variable [Monoid α] {a b u : α}

theorem dvd (hu : IsUnit u) : u ∣ a := by
  rcases hu with ⟨v, rfl⟩
  exact ⟨↑(v⁻¹) * a, by simp [mul_assoc]⟩
