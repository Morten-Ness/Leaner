import Mathlib

variable {α : Type*}

variable [CommSemigroup α] {a b c : α}

theorem dvd_iff_exists_eq_mul_left : a ∣ b ↔ ∃ c, b = c * a := ⟨exists_eq_mul_left_of_dvd, by
    rintro ⟨c, rfl⟩
    exact ⟨c, mul_comm _ _⟩⟩

