import Mathlib

variable {α : Type u}

variable [Monoid α] {a : α}

theorem val_div_eq_divp (u₁ u₂ : αˣ) : ↑(u₁ / u₂) = ↑u₁ /ₚ u₂ := by
  rw [divp, division_def, Units.val_mul]

