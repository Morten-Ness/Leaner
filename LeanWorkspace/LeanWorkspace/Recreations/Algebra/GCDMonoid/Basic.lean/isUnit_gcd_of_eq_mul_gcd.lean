import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem isUnit_gcd_of_eq_mul_gcd {α : Type*} [CommMonoidWithZero α] [GCDMonoid α]
    {x y x' y' : α} (ex : x = gcd x y * x') (ey : y = gcd x y * y') (h : gcd x y ≠ 0) :
    IsUnit (gcd x' y') := by
  rw [← associated_one_iff_isUnit]
  refine Associated.of_mul_left ?_ (Associated.refl <| gcd x y) h
  convert (gcd_mul_left' (gcd x y) x' y').symm using 1
  rw [← ex, ← ey, mul_one]

