import Mathlib

variable {R : Type u}

theorem toNonUnitalNonAssocRing_injective :
    Function.Injective (@toNonUnitalNonAssocRing R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

