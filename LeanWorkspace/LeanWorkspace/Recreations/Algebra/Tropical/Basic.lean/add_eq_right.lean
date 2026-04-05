import Mathlib

variable (R : Type u)

variable [LinearOrder R]

theorem add_eq_right ⦃x y : Tropical R⦄ (h : y ≤ x) : x + y = y := Tropical.untrop_injective (by simpa using h)

