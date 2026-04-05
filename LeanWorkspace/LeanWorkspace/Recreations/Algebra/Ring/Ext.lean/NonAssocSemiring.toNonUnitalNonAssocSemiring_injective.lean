import Mathlib

variable {R : Type u}

theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  intro _ _ _
  ext <;> congr

