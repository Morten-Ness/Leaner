import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_mul_lcm [GCDMonoid α] : ∀ a b : α, Associated (gcd a b * lcm a b) (a * b) := GCDMonoid.gcd_mul_lcm

