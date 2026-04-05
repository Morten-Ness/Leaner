import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_dvd_lcm_mul_right [GCDMonoid α] (m n k : α) : lcm m n ∣ lcm (m * k) n := lcm_dvd_lcm (dvd_mul_right _ _) dvd_rfl

