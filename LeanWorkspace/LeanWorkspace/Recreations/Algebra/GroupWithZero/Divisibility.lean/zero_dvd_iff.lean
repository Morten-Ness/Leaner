import Mathlib

variable {α : Type*}

variable [SemigroupWithZero α] {a : α}

theorem zero_dvd_iff : 0 ∣ a ↔ a = 0 := ⟨eq_zero_of_zero_dvd, fun h => by
    rw [h]
    exact ⟨0, by simp⟩⟩

