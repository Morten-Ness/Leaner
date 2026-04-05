import Mathlib

variable (R : Type u)

variable [LinearOrder R]

theorem inf_eq_add : ((· ⊓ ·) : Tropical R → Tropical R → Tropical R) = (· + ·) := rfl

