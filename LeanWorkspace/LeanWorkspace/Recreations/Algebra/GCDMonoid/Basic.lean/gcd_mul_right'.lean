import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_mul_right' [GCDMonoid α] (a b c : α) :
    Associated (gcd (b * a) (c * a)) (gcd b c * a) := by
  simp only [mul_comm, gcd_mul_left']

