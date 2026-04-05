import Mathlib

variable {R : Type u}

theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

