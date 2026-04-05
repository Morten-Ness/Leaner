import Mathlib

variable {R : Type u}

theorem toNonUnitalRing_injective :
    Function.Injective (@toNonUnitalRing R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

