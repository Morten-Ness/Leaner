import Mathlib

variable {α : Type*}

variable [CommMonoid α] {a b : α}

theorem pow_dvd_pow_of_dvd_of_le {m n : ℕ} (hab : a ∣ b) (hmn : m ≤ n) : a ^ m ∣ b ^ n := by
  trans (a ^ n) <;> [gcongr; apply_rules [pow_dvd_pow_of_dvd]]

