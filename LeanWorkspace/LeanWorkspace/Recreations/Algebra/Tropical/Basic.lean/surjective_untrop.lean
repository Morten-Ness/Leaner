import Mathlib

variable (R : Type u)

theorem surjective_untrop : Function.Surjective (Tropical.untrop : Tropical R → R) := Tropical.tropEquiv.symm.surjective

