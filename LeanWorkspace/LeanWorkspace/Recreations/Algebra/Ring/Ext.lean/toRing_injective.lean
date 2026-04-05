import Mathlib

variable {R : Type u}

theorem toRing_injective : Function.Injective (@toRing R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

