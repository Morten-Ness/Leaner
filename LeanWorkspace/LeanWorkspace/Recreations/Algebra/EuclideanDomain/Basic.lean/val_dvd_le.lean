import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem val_dvd_le : ∀ a b : R, b ∣ a → a ≠ 0 → ¬a ≺ b
  | _, b, ⟨d, rfl⟩, ha => mul_left_not_lt b (mt (by rintro rfl; exact mul_zero _) ha)
