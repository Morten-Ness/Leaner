import Mathlib

variable (R : Type u)

theorem untrop_zpow [AddGroup R] (x : Tropical R) (n : ℤ) : Tropical.untrop (x ^ n) = n • Tropical.untrop x := rfl

