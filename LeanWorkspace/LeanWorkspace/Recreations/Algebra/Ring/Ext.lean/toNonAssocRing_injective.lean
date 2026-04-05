import Mathlib

variable {R : Type u}

theorem toNonAssocRing_injective :
    Function.Injective (@toNonAssocRing R) := by
  intro _ _ _
  ext <;> congr

