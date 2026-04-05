import Mathlib

variable {α β : Type*}

variable [Semiring α] {a b c : α} {m n : ℕ}

theorem min_pow_dvd_add (ha : c ^ m ∣ a) (hb : c ^ n ∣ b) : c ^ min m n ∣ a + b := ((pow_dvd_pow c (m.min_le_left n)).trans ha).add ((pow_dvd_pow c (m.min_le_right n)).trans hb)

