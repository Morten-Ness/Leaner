import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_mul_right [NormalizedGCDMonoid α] (a b c : α) :
    gcd (b * a) (c * a) = gcd b c * normalize a := by simp only [mul_comm, gcd_mul_left]

