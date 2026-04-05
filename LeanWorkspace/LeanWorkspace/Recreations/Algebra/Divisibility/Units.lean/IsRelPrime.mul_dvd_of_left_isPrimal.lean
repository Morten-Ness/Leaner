import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

theorem IsRelPrime.mul_dvd_of_left_isPrimal (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z)
    (hx : IsPrimal x) : x * y ∣ z := by
  rw [mul_comm]; exact H.symm.mul_dvd_of_right_isPrimal H2 H1 hx

