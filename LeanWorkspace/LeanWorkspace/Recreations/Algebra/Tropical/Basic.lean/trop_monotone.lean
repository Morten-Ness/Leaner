import Mathlib

variable (R : Type u)

theorem trop_monotone [Preorder R] : Monotone (Tropical.trop : R → Tropical R) := fun _ _ => id

