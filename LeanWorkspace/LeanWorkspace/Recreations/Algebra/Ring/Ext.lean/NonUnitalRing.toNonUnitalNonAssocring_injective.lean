import Mathlib

variable {R : Type u}

theorem toNonUnitalNonAssocring_injective :
    Function.Injective (@toNonUnitalNonAssocRing R) := by
  intro _ _ _
  ext <;> congr

