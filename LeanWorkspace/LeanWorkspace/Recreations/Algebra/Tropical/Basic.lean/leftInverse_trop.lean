import Mathlib

variable (R : Type u)

theorem leftInverse_trop : Function.LeftInverse (Tropical.trop : R → Tropical R) Tropical.untrop := Tropical.trop_untrop

