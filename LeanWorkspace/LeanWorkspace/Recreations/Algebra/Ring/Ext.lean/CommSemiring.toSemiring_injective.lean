import Mathlib

variable {R : Type u}

theorem toSemiring_injective :
    Function.Injective (@toSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

