import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem dvd_div_of_mul_dvd {a b c : R} (h : a * b ∣ c) : b ∣ c / a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [div_zero, dvd_zero]
  rcases h with ⟨d, rfl⟩
  refine ⟨d, ?_⟩
  rw [mul_assoc, mul_div_cancel_left₀ _ ha]

