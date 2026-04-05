import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

theorem IsRelPrime.dvd_of_dvd_mul_right_of_isPrimal (H1 : IsRelPrime x z) (H2 : x ∣ y * z)
    (h : IsPrimal x) : x ∣ y := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h H2
  exact Units.mul_right_dvd (H1.of_mul_left_right.isUnit_of_dvd hb).mpr ha

