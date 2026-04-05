import Mathlib

variable {R : Type u}

theorem AddCommMonoidWithOne.toAddMonoidWithOne_injective :
    Function.Injective (@AddCommMonoidWithOne.toAddMonoidWithOne R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

