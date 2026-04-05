import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_dvd_lcm_mul_right_right [GCDMonoid α] (m n k : α) : lcm m n ∣ lcm m (n * k) := lcm_dvd_lcm dvd_rfl (dvd_mul_right _ _)

