import Mathlib

variable (R : Type u)

theorem add_pow [LinearOrder R] [AddMonoid R] [AddLeftMono R] [AddRightMono R]
    (x y : Tropical R) (n : ℕ) :
    (x + y) ^ n = x ^ n + y ^ n := by
  rcases le_total x y with h | h
  · rw [Tropical.add_eq_left h, Tropical.add_eq_left (pow_le_pow_left' h _)]
  · rw [Tropical.add_eq_right h, Tropical.add_eq_right (pow_le_pow_left' h _)]

