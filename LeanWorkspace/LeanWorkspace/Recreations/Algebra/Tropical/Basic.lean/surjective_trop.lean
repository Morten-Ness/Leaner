import Mathlib

variable (R : Type u)

theorem surjective_trop : Function.Surjective (Tropical.trop : R → Tropical R) := Tropical.tropEquiv.surjective

