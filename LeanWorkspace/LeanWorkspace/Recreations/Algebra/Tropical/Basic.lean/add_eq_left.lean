import Mathlib

variable (R : Type u)

variable [LinearOrder R]

theorem add_eq_left ⦃x y : Tropical R⦄ (h : x ≤ y) : x + y = x := Tropical.untrop_injective (by simpa using h)

