import Mathlib

variable (R : Type u)

variable [LinearOrder R]

theorem min_eq_add : (min : Tropical R → Tropical R → Tropical R) = (· + ·) := rfl

