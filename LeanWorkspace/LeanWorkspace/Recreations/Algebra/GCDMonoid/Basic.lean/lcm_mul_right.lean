import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_mul_right [NormalizedGCDMonoid α] (a b c : α) :
    lcm (b * a) (c * a) = lcm b c * normalize a := by simp only [mul_comm, lcm_mul_left]

