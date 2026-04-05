import Mathlib

variable {R : Type u}

theorem toNonUnitalRing_injective :
    Function.Injective (@toNonUnitalRing R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

