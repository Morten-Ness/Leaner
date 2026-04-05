import Mathlib

variable {R : Type u}

theorem toNonUnitalSemiring_injective :
    Function.Injective (@toNonUnitalSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

