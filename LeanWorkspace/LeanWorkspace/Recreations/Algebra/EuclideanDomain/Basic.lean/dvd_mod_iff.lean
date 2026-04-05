import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem dvd_mod_iff {a b c : R} (h : c ∣ b) : c ∣ a % b ↔ c ∣ a := by
  rw [← dvd_add_right (h.mul_right _), div_add_mod]

