import Mathlib

variable {α : Type*}

variable [Monoid α] {a b : α} {u : αˣ}

theorem coe_dvd : ↑u ∣ a := ⟨↑u⁻¹ * a, by simp⟩

