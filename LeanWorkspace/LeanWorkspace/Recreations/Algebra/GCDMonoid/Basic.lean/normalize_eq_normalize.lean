import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [NormalizationMonoid α]

theorem normalize_eq_normalize [IsCancelMulZero α] {a b : α} (hab : a ∣ b) (hba : b ∣ a) :
    normalize a = normalize b := by
  nontriviality α
  rcases associated_of_dvd_dvd hab hba with ⟨u, rfl⟩
  refine by_cases (by rintro rfl; simp) fun ha : a ≠ 0 => ?_
  suffices a * ↑(normUnit a) = a * ↑u * ↑(normUnit a) * ↑u⁻¹ by
    simpa only [normalize_apply, mul_assoc, normUnit_mul ha u.ne_zero, normUnit_coe_units]
  calc
    a * ↑(normUnit a) = a * ↑(normUnit a) * ↑u * ↑u⁻¹ := (Units.mul_inv_cancel_right _ _).symm
    _ = a * ↑u * ↑(normUnit a) * ↑u⁻¹ := by rw [mul_right_comm a]

