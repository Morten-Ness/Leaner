import Mathlib

variable (R : Type u)

theorem untrop_monotone [Preorder R] : Monotone (Tropical.untrop : Tropical R → R) := fun _ _ => id

