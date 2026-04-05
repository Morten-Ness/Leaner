import Mathlib

variable {α : Type*}

variable [CommMonoid α]

theorem dvd_pow_self_iff {x : α} {n : ℕ} :
    x ∣ x ^ n ↔ n ≠ 0 ∨ IsUnit x := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [isUnit_iff_dvd_one]
  · simp [hn, dvd_pow_self]

