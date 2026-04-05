import Mathlib

variable {α : Type*}

variable [Monoid α] {a b u : α}

theorem dvd (hu : IsUnit u) : u ∣ a := by
  rcases hu with ⟨u, rfl⟩
  apply Units.coe_dvd

