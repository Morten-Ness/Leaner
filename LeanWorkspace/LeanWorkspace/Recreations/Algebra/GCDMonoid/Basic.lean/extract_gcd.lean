import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem extract_gcd {α : Type*} [CommMonoidWithZero α] [GCDMonoid α] (x y : α) :
    ∃ x' y', x = gcd x y * x' ∧ y = gcd x y * y' ∧ IsUnit (gcd x' y') := by
  by_cases h : gcd x y = 0
  · obtain ⟨rfl, rfl⟩ := (gcd_eq_zero_iff x y).1 h
    simp_rw [← associated_one_iff_isUnit]
    exact ⟨1, 1, by rw [h, zero_mul], by rw [h, zero_mul], gcd_one_left' 1⟩
  obtain ⟨x', ex⟩ := gcd_dvd_left x y
  obtain ⟨y', ey⟩ := gcd_dvd_right x y
  exact ⟨x', y', ex, ey, isUnit_gcd_of_eq_mul_gcd ex ey h⟩

