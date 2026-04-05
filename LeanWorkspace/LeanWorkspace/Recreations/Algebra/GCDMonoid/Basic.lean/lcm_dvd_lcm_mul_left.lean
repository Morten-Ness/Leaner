import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_dvd_lcm_mul_left [GCDMonoid α] (m n k : α) : lcm m n ∣ lcm (k * m) n := lcm_dvd_lcm (dvd_mul_left _ _) dvd_rfl

