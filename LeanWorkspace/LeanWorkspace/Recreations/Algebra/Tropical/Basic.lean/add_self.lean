import Mathlib

variable (R : Type u)

variable [LinearOrder R]

theorem add_self (x : Tropical R) : x + x = x := Tropical.untrop_injective (min_eq_right le_rfl)

