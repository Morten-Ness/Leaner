import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_dvd_lcm_mul_left_right [GCDMonoid α] (m n k : α) : lcm m n ∣ lcm m (k * n) := lcm_dvd_lcm dvd_rfl (dvd_mul_left _ _)

